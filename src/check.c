#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include "ast.h"
#include "check.h"
#include "eval.h"
#include "expr.h"
#include "identifier.h"
#include "mod.h"
#include "scope.h"
#include "type_store.h"
#include "typedef.h"
#include "types.h"
#include "util.h"

struct ident *
mkident(struct context *ctx, struct ident *in, const char *symbol)
{
	if (symbol) {
		return intern_name(ctx->itbl, symbol);
	} else if (ctx->ns && in->ns == NULL) {
		return intern_ident(ctx->itbl, in->name, ctx->ns);
	} else {
		return in;
	}
}

static struct ident *
intern_generated(struct context *ctx, const char *template)
{
	const char *s = intern_owned(ctx->itbl, gen_name(&ctx->id, template));
	return intern_name(ctx->itbl, s);
}

void
mkstrliteral(struct expression *expr, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	size_t n = vsnprintf(NULL, 0, fmt, ap);
	va_end(ap);
	char *s = xcalloc(n + 1, n);
	va_start(ap, fmt);
	vsnprintf(s, n + 1, fmt, ap);
	va_end(ap);

	*expr = (struct expression) {
		.type = EXPR_LITERAL,
		.result = &builtin_type_str,
	};
	expr->literal.string.value = s;
	expr->literal.string.len = n;
}

char *
gen_typename(const struct type *type)
{
	size_t sz = 0;
	char *ptr = NULL;
	FILE *f = open_memstream(&ptr, &sz);
	if (f == NULL) {
		xfprintf(stderr, "Unable to open memstream: %s\n",
			strerror(errno));
		exit(EXIT_ABNORMAL);
	}
	emit_type(type, f);
	fclose(f);
	return ptr;
}

static void
handle_errors(struct errors *errors)
{
	struct errors *error = errors;
	while (error) {
		xfprintf(stderr, "%s:%d:%d: error: %s\n", sources[error->loc.file],
			error->loc.lineno, error->loc.colno, error->msg);
		errline(error->loc);
		free(error->msg);
		struct errors *next = error->next;
		free(error);
		error = next;
	}
	if (errors) {
		exit(EXIT_CHECK);
	}
}

static void
mkerror(struct expression *expr)
{
	expr->type = EXPR_LITERAL;
	expr->result = &builtin_type_error;
	expr->literal.uval = 0;
	expr->loc = (struct location){0};
}

static void
verror(struct context *ctx, const struct location loc,
		const char *fmt, va_list ap)
{
	va_list copy;
	va_copy(copy, ap);
	size_t sz = vsnprintf(NULL, 0, fmt, copy);
	va_end(copy);

	char *msg = xcalloc(sz + 1, 1);
	vsnprintf(msg, sz + 1, fmt, ap);

	struct errors *next = *ctx->next = xcalloc(1, sizeof(struct errors));
	next->loc = loc;
	next->msg = msg;
	ctx->next = &next->next;
}

void
error(struct context *ctx, struct location loc, struct expression *expr,
		const char *fmt, ...)
{
	if (expr) {
		mkerror(expr);
		expr->loc = loc;
	}
	va_list ap;
	va_start(ap, fmt);
	verror(ctx, loc, fmt, ap);
	va_end(ap);
}

FORMAT(3, 4) static noreturn void
error_norec(struct context *ctx, struct location loc, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	verror(ctx, loc, fmt, ap);
	va_end(ap);

	handle_errors(ctx->errors);
	abort();
}

struct expression *
lower_implicit_cast(struct context *ctx,
		const struct type *to, struct expression *expr)
{
	if (to == expr->result || expr->result->storage == STORAGE_NEVER) {
		return expr;
	}

	if (type_dealias(ctx, to)->storage == STORAGE_TAGGED) {
		const struct type *interim =
			tagged_select_subtype(ctx, to, expr->result, true);
		if (interim) {
			expr = lower_implicit_cast(ctx, interim, expr);
		}
	}

	struct expression *cast = xcalloc(1, sizeof(struct expression));
	cast->type = EXPR_CAST;
	cast->loc = expr->loc;
	cast->result = cast->cast.secondary = to;
	cast->cast.kind = C_CAST;
	cast->cast.value = expr;
	cast->cast.lowered = true;
	return cast;
}

static void resolve_decl(struct context *ctx, struct scope_object *obj);

static const struct type *
check_autodereference(struct context *ctx, struct location loc,
		const struct type *type)
{
	const struct type *dtype = type_dereference(ctx, type, false);
	if (dtype == NULL) {
		error(ctx, loc, NULL, "Cannot autodereference a nullable pointer");
	}
	return type_dereference(ctx, type, true);
}

static void
check_expr_access(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_ACCESS;
	expr->access.type = aexpr->access.type;

	struct scope_object *obj = NULL;
	switch (expr->access.type) {
	case ACCESS_IDENTIFIER:
		obj = scope_lookup(ctx->scope, aexpr->access.ident);
		if (!obj) {
			char buf[IDENT_BUFSIZ];
			ident_unparse_static(aexpr->access.ident, buf);
			error(ctx, aexpr->loc, expr,
				"Unknown object '%s'", buf);
			return;
		}
		wrap_resolver(ctx, obj, resolve_decl);

		switch (obj->otype) {
		case O_CONST:
			// Lower flexible types
			*expr = *obj->value;
			flexible_reset_refs(expr->result);
			break;
		case O_BIND:
		case O_DECL:
			expr->result = obj->type;
			expr->access.object = obj;
			break;
		case O_TYPE:
			if (type_dealias(ctx, obj->type)->storage != STORAGE_VOID &&
					type_dealias(ctx, obj->type)->storage != STORAGE_DONE) {
				char *ident = ident_unparse(obj->type->alias.ident);
				error(ctx, aexpr->loc, expr,
					"Cannot use non void or done type alias '%s' as literal",
					ident);
				free(ident);
				return;
			}
			expr->type = EXPR_LITERAL;
			expr->result = obj->type;
			break;
		case O_SCAN:
			assert(0); // handled above
		}
		break;
	case ACCESS_INDEX:
		expr->access.array = xcalloc(1, sizeof(struct expression));
		expr->access.index = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->access.array, expr->access.array, NULL);
		check_expression(ctx, aexpr->access.index, expr->access.index, &builtin_type_size);
		const struct type *atype = check_autodereference(ctx,
				aexpr->access.array->loc, expr->access.array->result);
		atype = type_dealias(ctx, atype);
		if (atype->storage == STORAGE_ERROR) {
			mkerror(expr);
			return;
		}
		const struct type *itype =
			type_dealias(ctx, expr->access.index->result);
		if (atype->storage != STORAGE_ARRAY
				&& atype->storage != STORAGE_SLICE) {
			error(ctx, aexpr->access.array->loc, expr,
				"Can only index into array or slice object, but got %s",
				type_storage_unparse(atype->storage));
			return;
		}
		if (atype->storage == STORAGE_SLICE
				&& atype->array.members->size == SIZE_UNDEFINED) {
			error(ctx, aexpr->access.array->loc, expr,
				"Cannot use index into slice whose member type has undefined size");
			return;
		}
		if (!type_is_integer(ctx, itype)) {
			error(ctx, aexpr->access.index->loc, expr,
				"Cannot use non-integer %s type as slice/array index",
				type_storage_unparse(itype->storage));
			return;
		}
		expr->access.index = lower_implicit_cast(ctx, 
			&builtin_type_size, expr->access.index);
		expr->result = type_store_lookup_with_flags(ctx,
			atype->array.members, atype->flags | atype->array.members->flags);

		// Compile-time bounds check
		if (atype->storage == STORAGE_ARRAY
				&& atype->array.length != SIZE_UNDEFINED) {
			struct expression *evaled = xcalloc(1, sizeof(struct expression));
			if (eval_expr(ctx, expr->access.index, evaled)) {
				if (evaled->literal.uval >= atype->array.length) {
					error(ctx, aexpr->loc, expr,
						"Index must be less than array length");
					free(evaled);
					return;
				}
				expr->access.bounds_checked = true;
			}
			free(evaled);
		}

		break;
	case ACCESS_FIELD:
		expr->access._struct = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->access._struct, expr->access._struct, NULL);
		const struct type *stype = check_autodereference(ctx,
			aexpr->access._struct->loc, expr->access._struct->result);
		stype = type_dealias(ctx, stype);
		if (stype->storage == STORAGE_ERROR) {
			mkerror(expr);
			return;
		}
		if (stype->storage != STORAGE_STRUCT
				&& stype->storage != STORAGE_UNION) {
			error(ctx, aexpr->access._struct->loc, expr,
				"Cannot select field from non-struct, non-union object");
			return;
		}
		expr->access.field = type_get_field(ctx, stype, aexpr->access.field);
		if (!expr->access.field) {
			error(ctx, aexpr->access._struct->loc, expr,
				"No such struct field '%s'", aexpr->access.field);
			return;
		}
		expr->result = expr->access.field->type;
		break;
	case ACCESS_TUPLE:
		expr->access.tuple = xcalloc(1, sizeof(struct expression));
		struct expression *value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->access.tuple, expr->access.tuple, NULL);
		check_expression(ctx, aexpr->access.value, value, NULL);
		assert(value->type == EXPR_LITERAL);

		const struct type *ttype = check_autodereference(ctx,
			aexpr->access.tuple->loc, expr->access.tuple->result);
		ttype = type_dealias(ctx, ttype);
		if (ttype->storage == STORAGE_ERROR) {
			mkerror(expr);
			return;
		}
		if (ttype->storage != STORAGE_TUPLE) {
			error(ctx, aexpr->access.tuple->loc, expr,
				"Cannot select value from non-tuple object");
			return;
		}
		if (!type_is_integer(ctx, value->result)) {
			error(ctx, aexpr->access.tuple->loc, expr,
				"Cannot use non-integer literal to select tuple value");
			return;
		}

		expr->access.tvalue = type_get_value(ttype,
			aexpr->access.value->literal.uval);
		if (!expr->access.tvalue) {
			error(ctx, aexpr->access.tuple->loc, expr,
				"No such tuple value '%" PRIu64 "'",
				aexpr->access.value->literal.uval);
			return;
		}
		expr->access.tindex = aexpr->access.value->literal.uval;

		expr->result = expr->access.tvalue->type;
		break;
	}
}

static void
check_expr_alloc_init(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *inithint,
	bool nullable)
{
	// alloc(initializer) case
	check_expression(ctx, aexpr->alloc.init, expr->alloc.init, inithint);
	if (expr->alloc.init->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}

	const struct type *objtype = expr->alloc.init->result;
	if (type_dealias(ctx, objtype)->storage == STORAGE_ARRAY
			&& type_dealias(ctx, objtype)->array.expandable) {
		const struct type *atype = type_dealias(ctx, objtype);
		if (!inithint) {
			error(ctx, aexpr->loc, expr,
				"Cannot infer expandable array length without type hint");
			return;
		}
		const struct type *htype = type_dealias(ctx, inithint);
		if (htype->storage != STORAGE_ARRAY) {
			error(ctx, aexpr->loc, expr,
				"Cannot assign expandable array from non-array type");
			return;
		}
		assert(htype->array.members == atype->array.members);
		objtype = inithint;
	}
	if (type_is_flexible(objtype) && inithint) {
		const struct type *promoted =
			promote_flexible(ctx, objtype, inithint);
		if (promoted) {
			objtype = promoted;
		}
	} else if (inithint) {
		uint32_t objtype_id = type_dealias(ctx, objtype)->id;
		uint32_t inithint_id = type_dealias(ctx, inithint)->id;
		if (objtype_id == inithint_id) {
			objtype = inithint;
		}
	}

	expr->alloc.allocation_result = type_store_lookup_pointer(ctx,
		aexpr->loc, objtype, nullable);

	if (expr->alloc.init->result->size == SIZE_UNDEFINED) {
		error(ctx, aexpr->loc, expr,
			"Cannot allocate object of undefined size");
		return;
	}
}

static void
check_expr_alloc_cap(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *inithint)
{
	// alloc(init, length/capacity) case
	check_expression(ctx, aexpr->alloc.init, expr->alloc.init, inithint);
	if (expr->alloc.init->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}

	const struct type *objtype = expr->alloc.init->result;
	if (type_dealias(ctx, objtype)->storage == STORAGE_ARRAY) {
		if (type_dealias(ctx, objtype)->array.length == SIZE_UNDEFINED) {
			error(ctx, aexpr->alloc.init->loc, expr,
				"Slice initializer must have defined length");
			return;
		}
	} else if (type_dealias(ctx, objtype)->storage != STORAGE_SLICE) {
		error(ctx, aexpr->alloc.init->loc, expr,
			"Slice initializer must be of slice or array type, not %s",
			type_storage_unparse(type_dealias(ctx, objtype)->storage));
		return;
	}

	const struct type *caphint = &builtin_type_size;
	expr->alloc.cap = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->alloc.cap, expr->alloc.cap, caphint);

	const struct type *captype = expr->alloc.cap->result;
	if (!type_is_assignable(ctx, &builtin_type_size, captype)) {
		error(ctx, aexpr->alloc.cap->loc, expr,
			"Slice capacity must be assignable to size");
		return;
	}
	expr->alloc.cap = lower_implicit_cast(ctx, &builtin_type_size, expr->alloc.cap);

	struct expression cap = {0};
	if (expr->alloc.init->type == EXPR_LITERAL
			&& expr->alloc.cap->type == EXPR_LITERAL
			&& eval_expr(ctx, expr->alloc.cap, &cap)) {
		uint64_t len = 0;
		for (struct array_literal *c = expr->alloc.init->literal.array;
				c != NULL; c = c->next) {
			len++;
		}
		if (cap.literal.uval < len) {
			error(ctx, aexpr->alloc.cap->loc, expr,
				"Slice capacity cannot be smaller than length of initializer");
			return;
		}
	}

	const struct type *membtype = type_dealias(ctx, objtype)->array.members;
	expr->alloc.allocation_result = type_store_lookup_slice(ctx,
		aexpr->alloc.init->loc, membtype);

	if (objtype->storage == STORAGE_ARRAY
			&& objtype->array.expandable) {
		expr->alloc.kind = ALLOC_LEN;
	}
}

static void
check_expr_alloc_copy(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *inithint)
{
	// alloc(init...) case
	check_expression(ctx, aexpr->alloc.init, expr->alloc.init, inithint);
	if (expr->alloc.init->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}

	const struct type *result = type_dealias(ctx, expr->alloc.init->result);
	if (result->storage != STORAGE_ARRAY
			&& result->storage != STORAGE_SLICE) {
		error(ctx, aexpr->alloc.init->loc, expr,
			"Slice initializer must be of slice or array type, not %s",
			type_storage_unparse(result->storage));
		return;
	}

	result = type_dealias(ctx, expr->alloc.init->result);
	expr->alloc.allocation_result = type_store_lookup_slice(ctx,
			aexpr->alloc.init->loc, result->array.members);
}

static void
alloc_inithint(struct context *ctx,
	const struct type *hint,
	enum alloc_kind kind,
	const struct type **inithint,
	bool *nullable)
{
	const struct type *htype = NULL;
	hint = type_dealias(ctx, hint);

	switch (hint->storage) {
	case STORAGE_TAGGED:;
		const struct type_tagged_union *first = &hint->tagged,
			*second = first->next;

		if (second->next != NULL) {
			*inithint = NULL;
			return;
		}

		if (first->type == &builtin_type_nomem) {
			htype = second->type;
		} else if (second->type == &builtin_type_nomem) {
			htype = first->type;
		} else {
			*inithint = NULL;
			return;
		}

		break;
	case STORAGE_POINTER:
	case STORAGE_SLICE:
		// handle cases such as
		// let a: alloc(0) as *u8;
		// let b: []u8 = alloc([0])!;
		htype = hint;
		break;
	default:
		*inithint = NULL;
		return;
	}

	switch (htype->storage) {
	case STORAGE_POINTER:
		if (kind == ALLOC_OBJECT) {
			*inithint = htype->pointer.referent;
			*nullable = htype->pointer.nullable;
		}
		break;
	case STORAGE_SLICE:
		*inithint = hint;
		break;
	default:
		*inithint = NULL;
		return;
	};
}

static void
check_expr_alloc(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	assert(aexpr->type == EXPR_ALLOC);
	expr->type = EXPR_ALLOC;
	expr->result = &builtin_type_void;
	expr->alloc.init = xcalloc(1, sizeof(struct expression));
	expr->alloc.kind = aexpr->alloc.kind;

	const struct type *inithint = NULL;
	bool nullable = false;

	if (hint != NULL) {
		alloc_inithint(ctx, hint, expr->alloc.kind, &inithint, &nullable);
	}

	switch (aexpr->alloc.kind) {
	case ALLOC_OBJECT:
		check_expr_alloc_init(ctx, aexpr, expr, inithint, nullable);
		break;
	case ALLOC_CAP:
		check_expr_alloc_cap(ctx, aexpr, expr, inithint);
		break;
	case ALLOC_COPY:
		check_expr_alloc_copy(ctx, aexpr, expr, inithint);
		break;
	case ALLOC_LEN:
		abort(); // Not determined by parse
	}

	if (expr->result == &builtin_type_error) {
		return;
	}

	struct type_tagged_union nomem_tag = {
		.type = &builtin_type_nomem,
		.next = NULL,
	};
	struct type_tagged_union tags = {
		.type = expr->alloc.allocation_result,
		.next = &nomem_tag,
	};
	expr->result = type_store_lookup_tagged(ctx, aexpr->loc, &tags);
}

static void
check_expr_append_insert(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	assert(aexpr->type == EXPR_APPEND || aexpr->type == EXPR_INSERT);
	expr->type = aexpr->type;

	struct type_tagged_union nomem_tag = {
		.type = &builtin_type_nomem,
		.next = NULL,
	};
	struct type_tagged_union tags = {
		.type = &builtin_type_void,
		.next = &nomem_tag,
	};

	expr->result = type_store_lookup_tagged(ctx, aexpr->loc, &tags);

	expr->append.is_static = aexpr->append.is_static;
	expr->append.is_multi = aexpr->append.is_multi;
	expr->append.object = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->append.object, expr->append.object, NULL);
	if (expr->append.object->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	if (expr->append.object->type != EXPR_ACCESS) {
		error(ctx, aexpr->append.object->loc, expr,
			"Expression must operate on an object");
		return;
	}

	const struct type *sltype;
	const struct type *sltypename;
	const char *exprtype_name;
	struct expression *object = NULL;
	switch (expr->type) {
	case EXPR_APPEND:
		sltypename = expr->append.object->result;
		exprtype_name = "append";

		object = expr->append.object;
		break;
	case EXPR_INSERT:
		assert(expr->append.object->type == EXPR_ACCESS);
		assert(expr->append.object->access.type == ACCESS_INDEX);
		sltypename = expr->append.object->access.array->result;
		exprtype_name = "insert";

		object = expr->append.object->access.array;
		break;
	default:
		abort(); // Invariant
	}

	if (object->type == EXPR_ACCESS
			&& object->access.type == ACCESS_IDENTIFIER
			&& object->access.object->flags &
				SO_FOR_EACH_SUBJECT) {
		error(ctx, aexpr->append.object->loc, expr,
			"cannot %s the subject of for-each loop", exprtype_name);
	}
	sltype = check_autodereference(ctx, aexpr->append.object->loc, sltypename);
	sltype = type_dealias(ctx, sltype);

	if (sltype->storage != STORAGE_SLICE) {
		char *typename = gen_typename(sltypename);
		error(ctx, aexpr->append.object->loc, expr,
			"%s expression must operate on a slice, but got %s",
			exprtype_name, typename);
		free(typename);
		return;
	}
	if (sltype->array.members->size == SIZE_UNDEFINED) {
		error(ctx, aexpr->append.object->loc, expr,
			"Cannot %s %sto slice whose member type has undefined size",
			exprtype_name, expr->type == EXPR_APPEND ? "" : "in");
		return;
	}

	expr->append.value = xcalloc(1, sizeof(struct expression));

	if (!expr->append.is_multi && !aexpr->append.length) {
		check_expression(ctx, aexpr->append.value, expr->append.value,
				sltype->array.members);
		if (!type_is_assignable(ctx, sltype->array.members,
				expr->append.value->result)) {
			error(ctx, aexpr->append.value->loc, expr,
				"Value type must be assignable to object member type");
			return;
		}
		expr->append.value = lower_implicit_cast(ctx, 
			sltype->array.members, expr->append.value);
		return;
	}

	check_expression(ctx, aexpr->append.value, expr->append.value, sltype);
	const struct type *valtype = type_dealias(ctx, expr->append.value->result);
	if (aexpr->append.length) {
		if (valtype->storage != STORAGE_ARRAY
				|| !valtype->array.expandable) {
			error(ctx, aexpr->append.value->loc, expr,
				"Value must be an expandable array in append with length");
			return;
		}
		struct expression *len = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->append.length, len, &builtin_type_size);
		if (!type_is_assignable(ctx, &builtin_type_size, len->result)) {
			error(ctx, aexpr->append.length->loc, expr,
				"Length parameter must be assignable to size");
			return;
		}
		len = lower_implicit_cast(ctx, &builtin_type_size, len);
		expr->append.length = len;
	} else if (valtype->storage != STORAGE_SLICE
			&& valtype->storage != STORAGE_ARRAY) {
		error(ctx, aexpr->append.value->loc, expr,
			"Value must be an array or a slice in multi-valued %s",
			exprtype_name);
		return;
	} else if (valtype->size == SIZE_UNDEFINED) {
		error(ctx, aexpr->loc, expr, "Value array must be bounded");
		return;
	}
	if (sltype->array.members != valtype->array.members) {
		error(ctx, aexpr->loc, expr,
			"Value member type must match object member type");
		return;
	}
}

static void
check_assert(struct context *ctx,
	struct ast_expression_assert e,
	struct location loc,
	struct expression *expr)
{
	expr->result = &builtin_type_void;
	expr->type = EXPR_ASSERT;

	if (e.cond != NULL) {
		expr->assert.cond = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, e.cond, expr->assert.cond, &builtin_type_bool);
		loc = e.cond->loc;
		if (expr->assert.cond->result->storage == STORAGE_ERROR) {
			mkerror(expr);
			return;
		}
		if (type_dealias(ctx, expr->assert.cond->result)->storage != STORAGE_BOOL) {
			error(ctx, loc, expr, "Assertion condition must be boolean");
			return;
		}
	} else {
		if (!e.is_static) {
			expr->result = &builtin_type_never;
		}
	}
	if (e.message == NULL) {
		expr->assert.fixed_reason = ABORT_ANON_ASSERTION_FAILED;
	} else {
		expr->assert.message = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, e.message, expr->assert.message, &builtin_type_str);
		if (type_dealias(ctx, expr->assert.message->result)->storage != STORAGE_STRING) {
			error(ctx, e.message->loc, expr,
				"Assertion message must be string");
			return;
		}
	}

	if (e.is_static) {
		expr->type = EXPR_LITERAL;
		bool cond = false;
		if (expr->assert.cond != NULL) {
			struct expression out = {0}, msgout = {0};
			if (!eval_expr(ctx, expr->assert.cond, &out)) {
				error(ctx, e.cond->loc, expr,
					"Unable to evaluate static assertion condition at compile time");
				return;
			}
			if (expr->assert.message) {
				if (!eval_expr(ctx, expr->assert.message, &msgout)) {
					error(ctx, e.message->loc, expr,
						"Unable to evaluate static assertion message at compile time");
					return;
				}
			}
			assert(type_dealias(ctx, out.result)->storage == STORAGE_BOOL);
			cond = out.literal.bval;
		}
		// XXX: Should these abort immediately?
		if (!cond) {
			if (e.message != NULL) {
				error(ctx, loc, expr, "Static assertion failed: %.*s",
					(int)expr->assert.message->literal.string.len,
					expr->assert.message->literal.string.value);
			} else {
				error(ctx, loc, expr, "Static assertion failed");
			}
		}
	}
}

static void
check_expr_assert(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	check_assert(ctx, aexpr->assert, aexpr->loc, expr);
}

static void
check_binarithm_op(struct context *ctx, struct expression *expr,
		enum binarithm_operator op)
{
	const struct type *dealiased = type_dealias(ctx, expr->result);
	switch (op) {
	// Numeric arithmetic
	case BIN_DIV:
	case BIN_MINUS:
	case BIN_PLUS:
	case BIN_TIMES:
		if (!type_is_numeric(ctx, dealiased)) {
			error(ctx, expr->loc, expr,
				"Cannot perform arithmetic on non-numeric %s type",
				type_storage_unparse(dealiased->storage));
		}
		return;
	// Integer artithmetic
	case BIN_BAND:
	case BIN_BOR:
	case BIN_LSHIFT:
	case BIN_MODULO:
	case BIN_RSHIFT:
	case BIN_BXOR:
		if (!type_is_integer(ctx, dealiased)) {
			error(ctx, expr->loc, expr,
				"Cannot perform operation on non-integer %s type",
				type_storage_unparse(dealiased->storage));
		}
		return;
	// Logical arithmetic
	case BIN_LAND:
	case BIN_LOR:
	case BIN_LXOR:
		expr->result = &builtin_type_bool;
		if (dealiased->storage != STORAGE_BOOL) {
			error(ctx, expr->loc, expr,
				"Cannot perform logical arithmetic on non-bool %s type",
				type_storage_unparse(dealiased->storage));
		}
		return;
	case BIN_GREATER:
	case BIN_GREATEREQ:
	case BIN_LESS:
	case BIN_LESSEQ:
		expr->result = &builtin_type_bool;
		if (!type_is_numeric(ctx, dealiased)) {
			error(ctx, expr->loc, expr,
				"Cannot perform comparison on non-numeric %s type",
				type_storage_unparse(dealiased->storage));
		}
		return;
	case BIN_LEQUAL:
	case BIN_NEQUAL:
		expr->result = &builtin_type_bool;
		if (!type_is_numeric(ctx, dealiased) &&
				dealiased->storage != STORAGE_POINTER
				&& dealiased->storage != STORAGE_STRING
				&& dealiased->storage != STORAGE_BOOL
				&& dealiased->storage != STORAGE_RCONST
				&& dealiased->storage != STORAGE_RUNE) {
			error(ctx, expr->loc, expr,
				"Cannot perform equality test on %s type",
				type_storage_unparse(dealiased->storage));
		}
		return;
	}
}

static void
check_expr_assign(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_ASSIGN;
	expr->result = &builtin_type_void;
	expr->assign.op = aexpr->assign.op;

	struct expression *value = xcalloc(1, sizeof(struct expression));

	if (aexpr->assign.object == NULL) {
		assert(expr->assign.op == BIN_LEQUAL);
		check_expression(ctx, aexpr->assign.value, value, NULL);
		expr->assign.value = value;
		return;
	}

	struct expression *object = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->assign.object, object, NULL);
	check_expression(ctx, aexpr->assign.value, value, object->result);

	if (object->type == EXPR_LITERAL
			&& object->result != &builtin_type_error) {
		error(ctx, aexpr->assign.object->loc, expr,
			"Cannot assign to constant");
		return;
	}
	if (object->result->size == SIZE_UNDEFINED) {
		error(ctx, aexpr->loc, expr,
			"Cannot assign to object with undefined size");
		return;
	}
	if (!type_is_assignable(ctx, object->result, value->result)) {
		char *valtypename = gen_typename(value->result);
		char *objtypename = gen_typename(object->result);
		error(ctx, aexpr->loc, expr,
			"rvalue type (%s) is not assignable to lvalue (%s)",
			valtypename, objtypename);
		free(valtypename);
		free(objtypename);
		return;
	}
	if (expr->assign.op != BIN_LEQUAL) {
		check_binarithm_op(ctx, object, expr->assign.op);
	}

	if (object->type == EXPR_SLICE
			&& value->result->storage == STORAGE_ARRAY
			&& value->result->array.expandable) {
		expr->assign.value = value;
	} else {
		expr->assign.value =
			lower_implicit_cast(ctx, object->result, value);
	}
	expr->assign.object = object;
}

static const struct type *
type_promote(struct context *ctx, const struct type *a, const struct type *b)
{
	// Note: we must return either a, b, or NULL
	// TODO: There are likely some improperly handled edge cases around type
	// flags, both here and in the spec
	const struct type *da = type_store_lookup_with_flags(ctx, a, 0);
	const struct type *db = type_store_lookup_with_flags(ctx, b, 0);

	if (da == db) {
		const struct type *base = type_store_lookup_with_flags(ctx, a,
			a->flags | b->flags);
		assert(base == a || base == b);
		return base;
	}

	if (a->storage == STORAGE_ALIAS && b->storage == STORAGE_ALIAS) {
		return NULL;
	}

	da = type_dealias(ctx, da);
	db = type_dealias(ctx, db);

	if (da == db) {
		return a->storage == STORAGE_ALIAS ? a : b;
	}

	if (type_is_flexible(da) || type_is_flexible(db)) {
		return promote_flexible(ctx, a, b);
	}

	if (db->storage == STORAGE_ENUM && da->storage == db->alias.type->storage) {
		return b;
	}

	if (db->storage == STORAGE_ERROR) {
		return a;
	}

	switch (da->storage) {
	case STORAGE_ENUM:
		if (da->alias.type->storage == db->storage) {
			return a;
		}
		return NULL;
	case STORAGE_I8:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_INT:
		if (!type_is_integer(ctx, db) || !type_is_signed(ctx, db)
				|| db->size == da->size) {
			return NULL;
		}
		return da->size > db->size ? a : b;
	case STORAGE_U32:
	case STORAGE_U16:
	case STORAGE_U64:
	case STORAGE_UINT:
	case STORAGE_SIZE:
	case STORAGE_U8:
		if (da->storage == STORAGE_SIZE && db->storage == STORAGE_UINTPTR) {
			return db;
		}
		if (!type_is_integer(ctx, db) || type_is_signed(ctx, db)
				|| db->size == da->size) {
			return NULL;
		}
		return da->size > db->size ? a : b;
	case STORAGE_F32:
	case STORAGE_F64:
		if (!type_is_float(ctx, db) || db->size == da->size) {
			return NULL;
		}
		return da->size > db->size ? a : b;
	case STORAGE_POINTER:
		if (db->storage == STORAGE_NULL) {
			return a;
		}
		if (db->storage == STORAGE_UINTPTR) {
			return a;
		}
		if (db->storage != STORAGE_POINTER) {
			return NULL;
		}
		if (da->pointer.referent->storage == STORAGE_OPAQUE ||
				db->pointer.referent->storage == STORAGE_OPAQUE) {
			return a;
		}
		const struct type *r = type_promote(ctx,
			da->pointer.referent, db->pointer.referent);
		if (r == da->pointer.referent) {
			return a;
		}
		if (r == db->pointer.referent) {
			return b;
		}
		assert(r == NULL);
		return NULL;
	case STORAGE_NULL:
		if (db->storage == STORAGE_POINTER
				|| db->storage == STORAGE_UINTPTR) {
			return b;
		}
		return NULL;
	case STORAGE_ERROR:
	case STORAGE_NEVER:
		return b;
	case STORAGE_UINTPTR:
		if (db->storage == STORAGE_SIZE
				|| db->storage == STORAGE_NULL) {
			return a;
		}
		if (db->storage == STORAGE_POINTER) {
			return b;
		}
		return NULL;
	// Cannot be promoted
	case STORAGE_ARRAY:
	case STORAGE_BOOL:
	case STORAGE_DONE:
	case STORAGE_FUNCTION:
	case STORAGE_NOMEM:
	case STORAGE_OPAQUE:
	case STORAGE_RUNE:
	case STORAGE_SLICE:
	case STORAGE_STRING:
	case STORAGE_STRUCT:
	case STORAGE_TAGGED:
	case STORAGE_TUPLE:
	case STORAGE_UNION:
	case STORAGE_VALIST:
	case STORAGE_VOID:
		return NULL;
	// Handled above
	case STORAGE_ALIAS:
	case STORAGE_FCONST:
	case STORAGE_ICONST:
	case STORAGE_RCONST:
		assert(0);
	}
	assert(0);
}

static void resolve_enum_field(struct context *ctx, struct scope_object *obj);

static bool
type_has_default(struct context *ctx, const struct type *type)
{
	switch (type->storage) {
	case STORAGE_BOOL:
	case STORAGE_DONE:
	case STORAGE_ERROR:
	case STORAGE_F32:
	case STORAGE_F64:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_I8:
	case STORAGE_INT:
	case STORAGE_NOMEM:
	case STORAGE_RUNE:
	case STORAGE_SIZE:
	case STORAGE_SLICE:
	case STORAGE_STRING:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_U8:
	case STORAGE_UINT:
	case STORAGE_UINTPTR:
	case STORAGE_VOID:
		return true;
	case STORAGE_FUNCTION:
	case STORAGE_NEVER:
	case STORAGE_OPAQUE:
	case STORAGE_TAGGED:
	case STORAGE_VALIST:
		return false;
	case STORAGE_ARRAY:
		return type->array.length != SIZE_UNDEFINED
			&& type_has_default(ctx, type->array.members);
	case STORAGE_ENUM:
		for (struct scope_object *obj = type->_enum.values->objects;
				obj != NULL; obj = obj->lnext) {
			if (obj->otype == O_DECL) {
				continue;
			}
			if (obj->otype == O_SCAN) {
				wrap_resolver(ctx, obj, resolve_enum_field);
			}
			assert(obj->otype == O_CONST);
			if (obj->value->literal.uval == 0) {
				return true;
			}
		}
		return false;
	case STORAGE_POINTER:
		return type->pointer.nullable;
	case STORAGE_STRUCT:
	case STORAGE_UNION:
		for (struct struct_field *sf = type->struct_union.fields;
				sf != NULL; sf = sf->next) {
			if (!type_has_default(ctx, sf->type)) {
				return false;
			}
		}
		return true;
	case STORAGE_TUPLE:
		for (const struct type_tuple *t = &type->tuple;
				t != NULL; t = t->next) {
			if (!type_has_default(ctx, t->type)) {
				return false;
			}
		}
		return true;
	case STORAGE_ALIAS:
		return type_has_default(ctx, type_dealias(ctx, type));
	case STORAGE_FCONST:
	case STORAGE_ICONST:
	case STORAGE_NULL:
	case STORAGE_RCONST:
		abort(); // unreachable
	}
	abort(); // Unreachable
}

static void
check_expr_binarithm(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_BINARITHM;
	expr->binarithm.op = aexpr->binarithm.op;

	struct expression *lvalue = xcalloc(1, sizeof(struct expression)),
		*rvalue = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->binarithm.lvalue, lvalue, NULL);
	check_expression(ctx, aexpr->binarithm.rvalue, rvalue, NULL);
	if (lvalue->result->storage == STORAGE_ERROR
			|| rvalue->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}

	expr->result = type_promote(ctx, lvalue->result, rvalue->result);
	if (expr->result == NULL) {
		char *ltypename = gen_typename(lvalue->result);
		char *rtypename = gen_typename(rvalue->result);
		error(ctx, aexpr->loc, expr, "Cannot promote %s and %s",
			ltypename, rtypename);
		free(ltypename);
		free(rtypename);
		return;
	}
	expr->binarithm.lvalue = lower_implicit_cast(ctx, expr->result, lvalue);
	expr->binarithm.rvalue = lower_implicit_cast(ctx, expr->result, rvalue);

	check_binarithm_op(ctx, expr, expr->binarithm.op);
}

static void
create_unpack_bindings(struct context *ctx,
	const struct type *type,
	const struct location loc,
	const struct ast_binding_names *names,
	bool is_static,
	struct expression *expr)
{
	type = type_dealias(ctx, type);

	if (type->storage != STORAGE_TUPLE) {
		error(ctx, loc, expr,
			"Cannot unpack non-tuple type");
		return;
	}

	expr->binding.unpack = xcalloc(1, sizeof(struct binding_unpack));
	struct binding_unpack *unpack = expr->binding.unpack;
	const struct type_tuple *type_tuple = &type->tuple;

	while (names != NULL && type_tuple != NULL) {
		if (type_tuple->type->size == SIZE_UNDEFINED) {
			error(ctx, loc, expr,
				"Cannot create binding of undefined size");
			return;
		}
		if (names->name != NULL) {
			if (unpack->object != NULL) {
				unpack->next = xcalloc(1,
					sizeof(struct binding_unpack));
				unpack = unpack->next;
			}
			if (is_static) {
				// Generate a static declaration ident
				unpack->object = scope_insert(ctx->scope, O_DECL,
					intern_generated(ctx, "static.%d"),
					names->name, type_tuple->type, NULL);
			} else {
				unpack->object = scope_insert(ctx->scope,
					O_BIND, names->name, names->name,
					type_tuple->type, NULL);
			}
			unpack->offset = type_tuple->offset;
		}

		names = names->next;
		type_tuple = type_tuple->next;
	}

	if (expr->binding.unpack->object == NULL) {
		error(ctx, loc, expr,
			"Must have at least one non-underscore value when unpacking tuples");
		return;
	}
	if (type_tuple != NULL) {
		error(ctx, loc, expr,
			"Fewer bindings than tuple elements were provided when unpacking");
		return;
	}
	if (names != NULL) {
		error(ctx, loc, expr,
			"More bindings than tuple elements were provided when unpacking");
		return;
	}
}

static void
check_expr_binding(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	assert(aexpr->type == EXPR_BINDING || aexpr->type == EXPR_DEFINE);
	expr->type = aexpr->type;
	expr->result = &builtin_type_void;

	struct expression_binding *binding = &expr->binding;
	const struct ast_expression_binding *abinding = &aexpr->binding;
	while (abinding) {
		const struct type *type = NULL;
		if (abinding->type) {
			type = type_store_lookup_atype(ctx, abinding->type);
		}

		struct expression *initializer =
			xcalloc(1, sizeof(struct expression));
		check_expression(ctx, abinding->initializer, initializer, type);

		if (abinding->type
				&& abinding->type->storage == STORAGE_ARRAY
				&& abinding->type->array.contextual) {
			if (initializer->result->storage == STORAGE_ERROR) {
				// no-op
			} else if (initializer->result->storage != STORAGE_ARRAY) {
				error(ctx, aexpr->loc, expr,
					"Cannot infer array length from non-array type");
				return;
			} else if (initializer->result->array.members
					!= type->array.members) {
				char *inittype = gen_typename(initializer->result);
				char *bindingtype= gen_typename(type);
				error(ctx, aexpr->loc, expr,
					"Initializer of type %s is not assignable to binding type %s",
					inittype, bindingtype);
				free(inittype);
				free(bindingtype);
				return;
			}
			type = initializer->result;
		}

		if (expr->type == EXPR_DEFINE) {
			if (type) {
				initializer = lower_implicit_cast(
					ctx, type, initializer);
			}
			struct expression *value =
				xcalloc(1, sizeof(struct expression));
			if (!eval_expr(ctx, initializer, value)) {
				error(ctx, initializer->loc, value,
					"Unable to evaluate constant initializer at compile time");
				type = &builtin_type_error;
			}
			binding->initializer = value;
			assert(abinding->names.name != NULL);
			assert(abinding->names.next == NULL);
			binding->object = scope_insert(ctx->scope, O_CONST,
				abinding->names.name, abinding->names.name,
				NULL, value);
			goto done;
		}
		if (!type) {
			type = initializer->result;
			// XXX why is this needed?
			type = type_store_lookup_with_flags(ctx, type, 0);
		}
		if (abinding->names.next != NULL) {
			create_unpack_bindings(ctx, type,
				abinding->initializer->loc, &abinding->names,
				abinding->is_static, expr);
		} else if (abinding->names.name != NULL) {
			if (abinding->is_static) {
				// Generate a static declaration ident
				binding->object = scope_insert(ctx->scope, O_DECL,
					intern_generated(ctx, "static.%d"),
					abinding->names.name, type, NULL);
			} else {
				binding->object = scope_insert(ctx->scope, O_BIND,
					abinding->names.name, abinding->names.name,
					type, NULL);
			}
		}

		if (type->storage == STORAGE_NULL) {
			error(ctx, aexpr->loc, expr,
				"Null is not a valid type for a binding");
			return;
		}
		if (!type_is_assignable(ctx, type, initializer->result)) {
			char *inittype = gen_typename(initializer->result);
			char *bindingtype= gen_typename(type);
			error(ctx, aexpr->loc, expr,
				"Initializer of type %s is not assignable to binding type %s",
				inittype, bindingtype);
			free(inittype);
			free(bindingtype);
			return;
		}
		type = lower_flexible(ctx, type, NULL);
		if (type->size == SIZE_UNDEFINED) {
			error(ctx, aexpr->loc, expr,
				"Cannot create binding for type of undefined size");
			return;
		}
		binding->initializer = lower_implicit_cast(ctx, type, initializer);

		if (abinding->is_static) {
			struct expression *value =
				xcalloc(1, sizeof(struct expression));
			if (!eval_expr(ctx, binding->initializer, value)) {
				error(ctx, abinding->initializer->loc, expr,
					"Unable to evaluate static initializer at compile time");
				return;
			}
			// TODO: Free initializer
			binding->initializer = value;
		}

done:
		if (abinding->next) {
			binding->next = xcalloc(1,
				sizeof(struct expression_binding));
			binding = binding->next;
		}

		abinding = abinding->next;
	}
}

static void
check_expr_call(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_CALL;

	struct expression *lvalue = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->call.lvalue, lvalue, NULL);
	expr->call.lvalue = lvalue;

	const struct type *fntype = check_autodereference(ctx,
		aexpr->loc, lvalue->result);
	fntype = type_dealias(ctx, fntype);
	if (fntype->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	if (fntype->storage != STORAGE_FUNCTION) {
		error(ctx, aexpr->loc, expr, "Cannot call non-function type");
		return;
	}
	if (fntype->func.variadism != VARIADISM_HARE && aexpr->call.variadic) {
		error(ctx, aexpr->loc, expr,
			"Function type does not permit variadic argument list");
	}
	expr->result = fntype->func.result;

	struct call_argument *arg, **next = &expr->call.args;
	struct ast_expression_list *aarg = aexpr->call.args;
	struct type_func_param *param = fntype->func.params;
	while (param && aarg) {
		arg = *next = xcalloc(1, sizeof(struct call_argument));
		arg->value = xcalloc(1, sizeof(struct expression));

		struct ast_expression val;
		if (!param->next && fntype->func.variadism == VARIADISM_HARE
				&& !aexpr->call.variadic) {
			// lower the rest to an array
			val = (struct ast_expression){
				.loc = aarg->expr->loc,
				.type = EXPR_LITERAL,
				.literal = {
					.storage = STORAGE_ARRAY,
					.array.exprs = aarg,
				},
			};
		} else {
			val = *aarg->expr;
		}

		check_expression(ctx, &val, arg->value, param->type);
		if (!type_is_assignable(ctx, param->type, arg->value->result)) {
			char *argtypename = gen_typename(arg->value->result);
			char *paramtypename = gen_typename(param->type);
			error(ctx, val.loc, expr,
				"Argument type %s is not assignable to parameter type %s",
				argtypename, paramtypename);
			free(argtypename);
			free(paramtypename);
			return;
		}
		arg->value = lower_implicit_cast(ctx, param->type, arg->value);
		if (!param->next && fntype->func.variadism == VARIADISM_HARE) {
			return;
		}

		aarg = aarg->next;
		next = &arg->next;
		param = param->next;
	}
	while (param && param->default_value) {
		arg = *next = xcalloc(1, sizeof(struct call_argument));
		arg->value = param->default_value;
		next = &arg->next;
		param = param->next;
	}
	if (param) {
		if (fntype->func.variadism == VARIADISM_HARE && !param->next) {
			// No variadic arguments, lower to empty slice
			arg = *next = xcalloc(1, sizeof(struct call_argument));
			arg->value = xcalloc(1, sizeof(struct expression));
			*arg->value = (struct expression){
				.type = EXPR_LITERAL,
				.result = param->type,
				.literal = {
					.object = NULL,
					.slice.array = NULL,
					.slice.len = 0,
				},
			};
			return;
		} else if (param->default_value == NULL) {
			error(ctx, aexpr->loc, expr,
				"Not enough arguments for function call");
			return;
		}
	} else if (aarg) {
		if (fntype->func.variadism != VARIADISM_C) {
			error(ctx, aexpr->loc, expr,
				"Too many arguments for function call");
			return;
		}
		while (aarg) {
			arg = *next = xcalloc(1, sizeof(struct call_argument));
			arg->value = xcalloc(1, sizeof(struct expression));
			check_expression(ctx, aarg->expr, arg->value, NULL);
			aarg = aarg->next;
			next = &arg->next;
		}
	}
}

static void
check_expr_cast(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_CAST;
	expr->cast.kind = aexpr->cast.kind;
	struct expression *value = expr->cast.value =
		xcalloc(1, sizeof(struct expression));
	const struct type *secondary = expr->cast.secondary =
		type_store_lookup_atype(ctx, aexpr->cast.type);
	// TODO: Instead of allowing errors on casts to void, we should use a
	// different nonterminal
	check_expression(ctx, aexpr->cast.value, value,
			secondary == &builtin_type_void ? NULL : secondary);

	const struct type *primary = type_dealias(ctx, expr->cast.value->result);
	if (primary->storage == STORAGE_ERROR
			|| secondary->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	switch (aexpr->cast.kind) {
	case C_ASSERTION:
	case C_TEST:
		if (primary->storage == STORAGE_POINTER) {
			if (!primary->pointer.nullable) {
				error(ctx, aexpr->cast.value->loc, expr,
					"Expected a tagged union type or "
					"a nullable pointer");
				return;
			}
			if (secondary->storage != STORAGE_NULL
					&& (secondary->storage != STORAGE_POINTER
					|| primary->pointer.referent
						!= secondary->pointer.referent
					|| (secondary->pointer.nullable))) {
				error(ctx, aexpr->cast.type->loc, expr,
					"Can only type assert nullable pointer into non-nullable pointer of the same type or null");
				return;
			}
			break;
		}
		if (primary->storage != STORAGE_TAGGED) {
			error(ctx, aexpr->cast.value->loc, expr,
				"Expected a tagged union type or "
				"a nullable pointer");
			return;
		}
		// secondary type must be a strict subset or a
		// member of the primary type
		if (!((tagged_subset_compat(ctx, primary, secondary)
				|| tagged_select_subtype(ctx, primary, secondary, true))
				&& !tagged_subset_compat(ctx, secondary, primary))) {
			char *typename1 = gen_typename(secondary);
			char *typename2 = gen_typename(primary);
			error(ctx, aexpr->cast.type->loc, expr,
				"Type %s is not a valid member of tagged union type %s",
				typename1, typename2);
			free(typename1);
			free(typename2);
			return;
		}
		break;
	case C_CAST:;
		const struct type *intermediary =
			type_is_castable(ctx, secondary, value->result);
		if (intermediary == NULL) {
			char *primarytypename = gen_typename(value->result);
			char *secondarytypename = gen_typename(secondary);
			error(ctx, aexpr->cast.type->loc, expr,
				"Invalid cast from %s to %s",
				primarytypename, secondarytypename);
			free(primarytypename);
			free(secondarytypename);
			return;
		}
		// intermediary type is required when casting to tagged union
		// whose member is an alias of primary type, since gen.c asserts
		// that the primary type is a direct member of the tagged union.
		// The value is first cast to an intermediary type which is a
		// direct member of the tagged union, before being cast to the
		// tagged union itself.
		expr->cast.value = lower_implicit_cast(ctx, intermediary, value);
		break;
	}
	expr->result = aexpr->cast.kind == C_TEST? &builtin_type_bool : secondary;
}

static void
check_expr_array_literal(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	size_t len = 0;
	struct ast_expression_list *item = aexpr->literal.array.exprs;
	struct array_literal *cur, **next = &expr->literal.array;
	const struct type *type = NULL;
	if (hint) {
		hint = type_dealias(ctx, hint);

		size_t narray = 0;
		switch (hint->storage) {
		case STORAGE_ARRAY:
		case STORAGE_SLICE:
			type = hint->array.members;
			break;
		case STORAGE_TAGGED:
			for (const struct type_tagged_union *tu = &hint->tagged;
					tu; tu = tu->next) {
				const struct type *t = type_dealias(ctx, tu->type);
				if (t->storage == STORAGE_ARRAY
						|| t->storage == STORAGE_SLICE) {
					hint = t;
					type = hint->array.members;
					++narray;
				}
			}
			if (narray != 1) {
				type = hint = NULL;
			}
			break;
		default:
			hint = NULL;
			break;
		}
	}

	while (item) {
		struct expression *value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, item->expr, value, type);
		cur = *next = xcalloc(1, sizeof(struct array_literal));
		cur->value = value;

		if (!type) {
			type = value->result;
		} else {
			if (!type_is_assignable(ctx, type, value->result)) {
				char *typename1 = gen_typename(type);
				char *typename2 = gen_typename(value->result);
				error(ctx, item->expr->loc, expr,
					"Array members must be of a uniform type, previously seen %s, but now see %s",
					typename1, typename2);
				free(typename1);
				free(typename2);
				return;
			}
			if (!hint) {
				// The promote_flexible in
				// type_is_assignable might've caused the
				// type to change out from under our feet
				type = expr->literal.array->value->result;
			}
			cur->value = lower_implicit_cast(ctx, type, cur->value);
		}

		item = item->next;
		next = &cur->next;
		++len;
	}

	if (type == NULL) {
		error(ctx, aexpr->loc, expr, "Cannot infer array type from context, try casting it to the desired type");
		return;
	}
	expr->result = type_store_lookup_array(ctx, aexpr->loc,
			type, len, aexpr->literal.array.expand);
}

static void
check_expr_compound(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_COMPOUND;

	struct scope *scope = scope_push(&ctx->scope, SCOPE_COMPOUND);
	scope->hint = hint;
	expr->compound.scope = scope;

	if (aexpr->compound.label) {
		expr->compound.label = aexpr->compound.label;
		scope->label = aexpr->compound.label;
	}

	struct expressions *list = &expr->compound.exprs;
	struct expressions **next = &list->next;

	const struct ast_expression_list *alist = &aexpr->compound.list;
	struct expression *lexpr = NULL;
	while (alist) {
		lexpr = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, alist->expr, lexpr, NULL);
		if (type_has_error(ctx, lexpr->result)) {
			error(ctx, alist->expr->loc, lexpr,
				"Cannot ignore error here");
		}
		list->expr = lexpr;

		alist = alist->next;
		if (alist) {
			*next = xcalloc(1, sizeof(struct expressions));
			list = *next;
			next = &list->next;
		}
		if (alist && lexpr->result->storage == STORAGE_NEVER) {
			error(ctx, alist->expr->loc, expr,
				"Expression with result 'never' may not be followed by additional expressions");
		}
	}

	if (lexpr->result->storage != STORAGE_NEVER) {
		// Add implicit `yield void` if control reaches end of compound
		// expression.
		struct type_tagged_union *result =
			xcalloc(1, sizeof(struct type_tagged_union));
		result->type = &builtin_type_void;
		result->next = scope->results;
		scope->results = result;

		list->next = xcalloc(1, sizeof(struct expressions));
		struct ast_expression *yexpr = xcalloc(1, sizeof(struct ast_expression));
		yexpr->type = EXPR_YIELD;
		lexpr = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, yexpr, lexpr, NULL);
		list->next->expr = lexpr;
	}
	expr->result = type_store_reduce_result(ctx, aexpr->loc,
			scope->results);

	for (struct yield *yield = scope->yields; yield;) {
		*yield->expression = lower_implicit_cast(ctx, expr->result,
			*yield->expression);

		struct yield *next = yield->next;
		free(yield);
		yield = next;
	}

	assert(expr->result);
	scope_pop(&ctx->scope);
}

static void
check_expr_literal(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_LITERAL;
	enum type_storage storage = aexpr->literal.storage;
	expr->result = builtin_type_for_storage(storage);

	switch (aexpr->literal.storage) {
	case STORAGE_ICONST:
		expr->result = type_create_flexible(storage,
			aexpr->literal.ival, aexpr->literal.ival);
		/* fallthrough */
	case STORAGE_I8:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_INT:
		expr->literal.ival = aexpr->literal.ival;
		break;
	case STORAGE_U8:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_UINT:
	case STORAGE_SIZE:
		expr->literal.uval = aexpr->literal.uval;
		break;
	case STORAGE_RCONST:
		expr->result = type_create_flexible(storage,
			aexpr->literal.rune, aexpr->literal.rune);
		expr->literal.rune = aexpr->literal.rune;
		break;
	case STORAGE_BOOL:
		expr->literal.bval = aexpr->literal.bval;
		break;
	case STORAGE_DONE:
	case STORAGE_NOMEM:
	case STORAGE_NULL:
	case STORAGE_VOID:
		// No storage
		break;
	case STORAGE_ARRAY:
		check_expr_array_literal(ctx, aexpr, expr, hint);
		break;
	case STORAGE_STRING:
		expr->literal.string.len = aexpr->literal.string.len;
		expr->literal.string.value = xcalloc(1, aexpr->literal.string.len);
		memcpy(expr->literal.string.value, aexpr->literal.string.value,
			aexpr->literal.string.len);
		break;
	case STORAGE_FCONST:
		expr->result = type_create_flexible(storage,
			aexpr->literal.fval, aexpr->literal.fval);
		// fallthrough
	case STORAGE_F32:
	case STORAGE_F64:
		expr->literal.fval = aexpr->literal.fval;
		break;
	case STORAGE_ENUM:
	case STORAGE_ERROR:
	case STORAGE_UINTPTR:
	case STORAGE_ALIAS:
	case STORAGE_FUNCTION:
	case STORAGE_NEVER:
	case STORAGE_OPAQUE:
	case STORAGE_POINTER:
	case STORAGE_RUNE:
	case STORAGE_SLICE:
	case STORAGE_TAGGED:
	case STORAGE_TUPLE:
	case STORAGE_STRUCT:
	case STORAGE_UNION:
	case STORAGE_VALIST:
		assert(0); // Invariant
	}
}

static void
check_expr_defer(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_DEFER;
	expr->result = &builtin_type_void;
	expr->defer.deferred = xcalloc(1, sizeof(struct expression));
	expr->defer.scope = scope_push(&ctx->scope, SCOPE_DEFER);
	check_expression(ctx, aexpr->defer.deferred, expr->defer.deferred, NULL);
	if (type_has_error(ctx, expr->defer.deferred->result)) {
		error(ctx, aexpr->defer.deferred->loc, expr->defer.deferred,
			"Cannot ignore error here");
	}
	scope_pop(&ctx->scope);
}

static void
check_expr_delete(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_DELETE;
	expr->delete.is_static = aexpr->delete.is_static;
	expr->result = &builtin_type_void;
	struct expression *dexpr = expr->delete.expr =
		xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->delete.expr, expr->delete.expr, NULL);
	const struct type *otype = NULL;
	switch (dexpr->type) {
	case EXPR_SLICE:
		otype = dexpr->slice.object->result;
		break;
	case EXPR_ACCESS:
		if (dexpr->access.type != ACCESS_INDEX) {
			error(ctx, aexpr->delete.expr->loc, expr,
				"Deleted expression must be slicing or indexing expression");
			return;
		}
		struct expression *array = dexpr->access.array;
		if (array->type == EXPR_ACCESS
				&& array->access.type == ACCESS_IDENTIFIER
				&& array->access.object->flags &
					SO_FOR_EACH_SUBJECT) {
			error(ctx, aexpr->delete.expr->loc, expr,
				"cannot delete the subject of for-each loop");
		}
		otype = dexpr->access.array->result;
		break;
	default:
		error(ctx, aexpr->delete.expr->loc, expr,
			"Deleted expression must be slicing or indexing expression");
		return;
	}
	otype = check_autodereference(ctx, aexpr->loc, otype);
	otype = type_dealias(ctx, otype);
	if (otype->storage != STORAGE_SLICE) {
		error(ctx, aexpr->delete.expr->loc, expr,
			"delete must operate on a slice");
		return;
	}
}

static void
check_expr_control(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = aexpr->type;
	expr->result = &builtin_type_never;
	expr->control.label = aexpr->control.label;

	enum scope_class want;
	switch (expr->type) {
	case EXPR_BREAK:
	case EXPR_CONTINUE:
		want = SCOPE_LOOP;
		break;
	case EXPR_YIELD:
		want = SCOPE_COMPOUND;
		break;
	default:
		abort(); // Invariant
	}

	struct scope *scope = NULL;
	if (aexpr->control.label) {
		scope = scope_lookup_label(ctx->scope, aexpr->control.label);
		if (scope && scope->class != want) {
			error(ctx, aexpr->loc, NULL,
				"Selected expression must%s be a loop",
				want == SCOPE_COMPOUND ? " not" : "");
		}
	} else {
		scope = scope_lookup_class(ctx->scope, want);
	}
	if (scope) {
		if (expr->type == EXPR_BREAK) {
			scope->has_break = true;
		}

		struct scope *defer_scope =
			scope_lookup_class(ctx->scope, SCOPE_DEFER);
		if (defer_scope) {
			defer_scope = aexpr->control.label
				? scope_lookup_label(defer_scope, aexpr->control.label)
				: scope_lookup_class(defer_scope, want);
			if (scope == defer_scope) {
				error(ctx, aexpr->loc, NULL,
					"Cannot jump out of defer expression");
				// continue checking so other errors can be reported
			}
		}
	} else {
		const char *msg;
		switch (expr->type) {
		case EXPR_BREAK:
			msg = "No eligible loop to break from";
			break;
		case EXPR_CONTINUE:
			msg = "No eligible loop to continue to";
			break;
		case EXPR_YIELD:
			msg = "No eligible expression to yield from";
			break;
		default:
			assert(0); // Invariant
		}
		error(ctx, aexpr->loc, NULL, "%s", msg);
		// continue checking so other errors can be reported
	}
	expr->control.scope = scope;

	if (expr->type != EXPR_YIELD) {
		return;
	}

	expr->control.value = xcalloc(1, sizeof(struct expression));
	if (aexpr->control.value) {
		const struct type *hint = scope ? scope->hint : NULL;
		check_expression(ctx, aexpr->control.value,
			expr->control.value, hint);
	} else {
		expr->control.value->type = EXPR_LITERAL;
		expr->control.value->result = &builtin_type_void;
	}

	if (scope == NULL) {
		return;
	}

	struct type_tagged_union *result =
		xcalloc(1, sizeof(struct type_tagged_union));
	result->type = expr->control.value->result;
	result->next = scope->results;
	scope->results = result;

	struct yield *yield = xcalloc(1, sizeof(struct yield));
	yield->expression = &expr->control.value;
	yield->next = scope->yields;
	scope->yields = yield;
}

static void
check_expr_for_accumulator(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint,
	struct scope *scope)
{
	struct expression *bindings = NULL, *cond = NULL, *afterthought = NULL;

	if (aexpr->_for.bindings) {
		bindings = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->_for.bindings, bindings, NULL);
		if (bindings->result->storage == STORAGE_ERROR) {
			return;
		}
		assert(bindings->result->storage == STORAGE_VOID);
		expr->_for.bindings = bindings;
	}

	cond = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->_for.cond, cond, &builtin_type_bool);
	expr->_for.cond = cond;
	if (type_dealias(ctx, cond->result)->storage != STORAGE_BOOL
			&& cond->result->storage != STORAGE_ERROR) {
		error(ctx, aexpr->_for.cond->loc, expr,
			"Expected for condition to be boolean");
		return;
	}

	if (aexpr->_for.afterthought) {
		afterthought = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->_for.afterthought, afterthought, &builtin_type_void);
		if (type_has_error(ctx, afterthought->result)) {
			error(ctx, aexpr->_for.afterthought->loc, afterthought,
				"Cannot ignore error here");
		}
		expr->_for.afterthought = afterthought;
	}

	struct expression *body = xcalloc(1, sizeof(struct expression));
	expr->_for.body = body;
	check_expression(ctx, aexpr->_for.body, body, NULL);
	if (type_has_error(ctx, body->result)) {
		error(ctx, aexpr->_for.body->loc, body,
			"Cannot ignore error here");
	}

	expr->_for.body = body;
	struct expression evaled;
	if (eval_expr(ctx, expr->_for.cond, &evaled)) {
		if (evaled.literal.bval && !scope->has_break) {
			expr->result = &builtin_type_never;
		}
	}
}

static void
check_expr_for_each(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	struct expression *binding = xcalloc(1, sizeof(struct expression));
	struct expression *initializer = xcalloc(1, sizeof(struct expression));

	expr->_for.bindings = binding;
	binding->type = EXPR_BINDING;
	binding->result = &builtin_type_void;
	binding->binding.initializer = initializer;

	struct ast_expression_binding *abinding = &aexpr->_for.bindings->binding;

	const struct type *binding_type = NULL, *init_type_hint = NULL;

	if (abinding->type != NULL) {
		binding_type = type_store_lookup_atype(ctx, abinding->type);

		// Construct a type hint for the init expression. For example,
		// if the type hint is *int and we are in a &.., we would have
		// to do: *int -> int -> [_]int
		init_type_hint = binding_type;

		switch (expr->_for.kind) {
		case FOR_EACH_POINTER:
			init_type_hint = type_dealias(ctx, init_type_hint);
			if (init_type_hint->storage != STORAGE_POINTER) {
				error(ctx, aexpr->loc, expr,
					"Expected pointer type");
				return;
			}
			init_type_hint = init_type_hint->pointer.referent;
			// fallthrough
		case FOR_EACH_VALUE:
			init_type_hint = type_store_lookup_array(ctx, aexpr->loc,
				init_type_hint, SIZE_UNDEFINED, false);
			break;
		case FOR_EACH_ITERATOR: {
			struct type_tagged_union *tags;

			struct type_tagged_union *done_tagged = xcalloc(1,
				sizeof(struct type_tagged_union));
			done_tagged->type = &builtin_type_done;

			if (init_type_hint->storage == STORAGE_TAGGED) {
				tags = tagged_dup_tags(&init_type_hint->tagged);
			} else {
				tags = xcalloc(1,
					sizeof(struct type_tagged_union));
				tags->type = binding_type;
			}

			tags->next = done_tagged;
			init_type_hint = type_store_lookup_tagged(ctx,
				aexpr->loc, tags);
			break;
		}
		default:
			abort(); // unreachable
		}
	}
	check_expression(ctx, abinding->initializer, initializer, init_type_hint);

	const struct type *initializer_type = type_dealias(ctx,
		initializer->result);
	const struct type *var_type = binding_type;
	const struct type *initializer_result;

	switch (expr->_for.kind) {
	case FOR_EACH_POINTER:
		if (abinding->names.next != NULL) {
			error(ctx, abinding->initializer->loc, expr,
				"Cannot unpack tuple by pointer in for-each loop");
			return;
		}
		// fallthrough
	case FOR_EACH_VALUE:
		initializer_type = type_dealias(ctx, check_autodereference(ctx,
			abinding->initializer->loc, initializer_type));

		if (initializer_type->storage != STORAGE_ARRAY
				&& initializer_type->storage != STORAGE_SLICE) {
			error(ctx, abinding->initializer->loc, initializer,
				"Expected array or slice");
			return;
		}
		if (initializer_type->storage == STORAGE_ARRAY
				&& initializer_type->size == SIZE_UNDEFINED) {
			error(ctx, abinding->initializer->loc, initializer,
				"Cannot iterate over array of undefined size");
			return;
		}
		if (expr->_for.kind == FOR_EACH_VALUE) {
			initializer_result = initializer_type->array.members;
		} else {
			initializer_result = type_store_lookup_pointer(ctx,
				aexpr->loc, initializer_type->array.members, false);
		}
		break;
	case FOR_EACH_ITERATOR:
		if (initializer_type->storage != STORAGE_TAGGED) {
			error(ctx, abinding->initializer->loc, initializer,
				"Expected tagged union");
			return;
		}

		struct type_tagged_union *tags = tagged_dup_tags(
			&initializer_type->tagged);
		struct type_tagged_union *prev_tag = NULL;
		int done_tags_found = 0;

		// Reomve all done tags and aliases of it from the tagged
		// union.
		for (struct type_tagged_union *tu = tags; tu; tu = tu->next) {
			if (type_dealias(ctx, tu->type)->storage == STORAGE_DONE) {
				if (prev_tag != NULL) {
					prev_tag->next = tu->next;
				} else {
					tags = tu->next;
				}
				done_tags_found++;
			}
			prev_tag = tu;
		}
		if (done_tags_found != 1) {
			error(ctx, abinding->initializer->loc, initializer,
				"Tagged union must contain exactly one done type");
			return;
		}
		initializer_result = type_store_reduce_result(ctx,
			abinding->initializer->loc, tags);
		break;
	default:
		abort();
	}

	if (var_type == NULL) {
		var_type = initializer_result;
	}
	if (var_type->size == SIZE_UNDEFINED) {
		error(ctx, abinding->initializer->loc, binding,
			"Cannot create binding of undefined size");
		// error is recoverable
	}
	if (abinding->names.next != NULL) {
		create_unpack_bindings(ctx, var_type, initializer->loc,
			&abinding->names, abinding->is_static, binding);
	} else if (abinding->names.name != NULL) {
		binding->binding.object = scope_insert(ctx->scope, O_BIND,
			abinding->names.name, abinding->names.name, var_type, NULL);
	}

	if (binding_type != NULL && !type_is_assignable(ctx, var_type, initializer_result)) {
		error(ctx, aexpr->loc, expr,
			"Initializer is not assignable to binding type");
		return;
	}

	struct expression *body = xcalloc(1, sizeof(struct expression));
	expr->_for.body = body;

	if (expr->_for.kind != FOR_EACH_ITERATOR
			&& initializer->type == EXPR_ACCESS
			&& initializer->access.type == ACCESS_IDENTIFIER) {
		initializer->access.object->flags
			|= SO_FOR_EACH_SUBJECT;

		check_expression(ctx, aexpr->_for.body, body, NULL);

		initializer->access.object->flags
			&= ~(SO_FOR_EACH_SUBJECT);
	} else {
		check_expression(ctx, aexpr->_for.body, body, NULL);
	}

	if (type_has_error(ctx, body->result)) {
		error(ctx, aexpr->_for.body->loc, body,
			"Cannot ignore error here");
	}
}

static void
check_expr_for(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_FOR;
	expr->result = &builtin_type_void;
	expr->_for.kind = aexpr->_for.kind;

	struct scope *scope = scope_push(&ctx->scope, SCOPE_LOOP);
	expr->_for.scope = scope;

	if (aexpr->_for.label) {
		expr->_for.label = aexpr->_for.label;
		scope->label = aexpr->_for.label;
	}

	switch (expr->_for.kind) {
	case FOR_ACCUMULATOR:
		check_expr_for_accumulator(ctx, aexpr, expr, hint, scope);
		break;
	case FOR_EACH_VALUE:
	case FOR_EACH_POINTER:
	case FOR_EACH_ITERATOR:
		check_expr_for_each(ctx, aexpr, expr, hint);
		break;
	}

	scope_pop(&ctx->scope);
}

static void
check_expr_free(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	assert(aexpr->type == EXPR_FREE);
	expr->type = EXPR_FREE;
	expr->free.expr = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->free.expr, expr->free.expr, NULL);

	if (expr->free.expr->type == EXPR_ACCESS
			&& expr->free.expr->access.type == ACCESS_IDENTIFIER
			&& expr->free.expr->access.object->flags
				& SO_FOR_EACH_SUBJECT) {
		error(ctx, aexpr->free.expr->loc, expr,
			"cannot free the subject of for-each loop");
	}

	enum type_storage storage = type_dealias(ctx, expr->free.expr->result)->storage;
	if (storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	if (storage != STORAGE_SLICE
			&& storage != STORAGE_STRING
			&& storage != STORAGE_POINTER
			&& storage != STORAGE_NULL) {
		error(ctx, aexpr->free.expr->loc, expr,
			"free must operate on slice, string, pointer, or null");
		return;
	}
	expr->result = &builtin_type_void;
}

static void
check_expr_if(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_IF;

	struct expression *cond, *true_branch, *false_branch;

	cond = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->_if.cond, cond, &builtin_type_bool);

	true_branch = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->_if.true_branch, true_branch, hint);
	false_branch = xcalloc(1, sizeof(struct expression));
	if (aexpr->_if.false_branch) {
		check_expression(ctx, aexpr->_if.false_branch, false_branch, hint);
	} else {
		false_branch->type = EXPR_LITERAL;
		false_branch->result = &builtin_type_void;
	}
	const struct type *fresult = false_branch->result;
	if (hint && type_is_assignable(ctx, hint, true_branch->result)
			&& type_is_assignable(ctx, hint, fresult)) {
		expr->result = hint;
	} else {
		struct type_tagged_union _tags = {
			.type = fresult,
			.next = NULL,
		}, tags = {
			.type = true_branch->result,
			.next = &_tags,
		};
		expr->result = type_store_reduce_result(ctx, aexpr->loc, &tags);
		if (expr->result == NULL) {
			error(ctx, aexpr->loc, expr,
				"Invalid result type (dangling or ambiguous null)");
			return;
		}
	}
	true_branch = lower_implicit_cast(ctx, expr->result, true_branch);
	false_branch = lower_implicit_cast(ctx, expr->result, false_branch);

	if (cond->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	if (type_dealias(ctx, cond->result)->storage != STORAGE_BOOL) {
		error(ctx, aexpr->_if.cond->loc, expr,
			"Expected if condition to be boolean");
		return;
	}

	expr->_if.cond = cond;
	expr->_if.true_branch = true_branch;
	expr->_if.false_branch = false_branch;
}

static const char *
check_match_case_nullable_ptr(struct context *ctx,
	const struct type *ctype,
	const struct type *ref_type)
{
	// match (e: nullable *ref_type) {
	// case ctype =>
	// Null has already been handled.
	if (ctype->storage != STORAGE_POINTER) {
		return "Match on nullable pointer: case is not null or pointer type";
	} else if (ref_type != type_dealias(ctx, ctype->pointer.referent)) {
		return "Match on nullable pointer: case has invalid pointer type";
	}
	return NULL;
}

static const char *
check_match_case_tagged(struct context *ctx,
	const struct type *ctype,
	const struct type *type)
{
	// match (e: type) {
	// case ctype =>
	// TODO: Assign a score to tagged compatibility
	// and choose the branch with the highest score.
	if (!type_is_assignable(ctx, type, ctype)) {
		return "Match on tagged union: case is not assignable to match type";
	}
	return NULL;
}

static const char *
check_match_case_tagged_ptr(struct context *ctx,
	const struct type *ctype,
	const struct type *ref_type)
{
	// match (e: *ref_type) {
	// case ctype =>
	if (ctype->size == 0) {
		if (!type_is_assignable(ctx, ref_type, ctype)) {
			return "Match on pointer to tagged union: zero-sized case type is not assignable to match type";
		}
	} else if (ctype->storage != STORAGE_POINTER) {
		return "Match on pointer to tagged union: finite-sized case type is not a pointer";
	} else if (!type_is_assignable(ctx, ref_type, ctype->pointer.referent)) {
		return "Match on pointer to tagged union: case is not assignable to match type";
	}
	return NULL;
}

static void
check_expr_match(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_MATCH;

	struct expression *value = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->match.value, value, NULL);
	expr->match.value = value;

	const struct type *type = type_dealias(ctx, value->result);
	if (type->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	bool is_tagged = type->storage == STORAGE_TAGGED;
	bool is_nullable_ptr = false, is_tagged_ptr = false;
	const struct type *ref_type = NULL;
	if (type->storage == STORAGE_POINTER) {
		is_nullable_ptr = type->pointer.nullable;
		ref_type = type_dealias(ctx, type->pointer.referent);
		if (ref_type->storage == STORAGE_ERROR) {
			mkerror(expr);
			return;
		}
		is_tagged_ptr = ref_type->storage == STORAGE_TAGGED;

	}
	if (!is_tagged && !is_nullable_ptr && !is_tagged_ptr) {
		error(ctx, aexpr->match.value->loc, expr,
			"Match value is not tagged union, pointer to tagged union, or nullable pointer type");
		return;
	}

	struct type_tagged_union result_type = {0};
	struct type_tagged_union *tagged = &result_type,
		**next_tag = &tagged->next;

	struct match_case **next = &expr->match.cases, *_case = NULL;
	for (struct ast_match_case *acase = aexpr->match.cases;
			acase; acase = acase->next) {
		_case = *next = xcalloc(1, sizeof(struct match_case));
		next = &_case->next;

		const struct type *ctype = NULL;
		if (acase->type) {
			ctype = type_store_lookup_atype(ctx, acase->type);
			const char *err_msg = NULL;
			if (ctype->storage == STORAGE_NULL && is_nullable_ptr) {
				// Ok in all cases.
			} else if (is_nullable_ptr && !is_tagged_ptr) {
				err_msg = check_match_case_nullable_ptr(ctx,
					ctype, ref_type);
			} else if (is_tagged_ptr) {
				err_msg = check_match_case_tagged_ptr(ctx,
					ctype, ref_type);
			} else {
				assert(is_tagged);
				err_msg = check_match_case_tagged(ctx,
					ctype, type);
			}
			if (err_msg) {
				error(ctx, acase->type->loc, expr, "%s", err_msg);
				return;
			}
		}

		if (acase->name != NULL) {
			assert(ctype);
			if (ctype->size == SIZE_UNDEFINED) {
				error(ctx, acase->type->loc, expr,
					"Cannot create binding for type of undefined size");
				return;
			}
			if (ctype->storage == STORAGE_NULL) {
				error(ctx, aexpr->loc, expr,
					"Null is not a valid type for a binding");
				return;
			}
			struct scope *scope = scope_push(&ctx->scope, SCOPE_MATCH);
			_case->object = scope_insert(scope, O_BIND, acase->name,
				acase->name, ctype, NULL);
		}

		_case->value = xcalloc(1, sizeof(struct expression));
		_case->type = ctype;

		// Lower to compound
		// TODO: This should probably be done in a more first-class way
		struct ast_expression compound = {
			.type = EXPR_COMPOUND,
			.loc = acase->exprs.expr->loc,
			.compound = {
				.label = aexpr->match.label,
				.list = acase->exprs,
			},
		};
		check_expression(ctx, &compound, _case->value, hint);

		if (acase->name != NULL) {
			scope_pop(&ctx->scope);
		}

		if (expr->result == NULL) {
			expr->result = _case->value->result;
			tagged->type = expr->result;
		} else if (expr->result != _case->value->result) {
			tagged = *next_tag =
				xcalloc(1, sizeof(struct type_tagged_union));
			next_tag = &tagged->next;
			tagged->type = _case->value->result;
		}
	}

	if (result_type.next) {
		if (hint) {
			expr->result = hint;
		} else {
			expr->result = type_store_reduce_result(
				ctx, aexpr->loc, &result_type);
			if (expr->result == NULL) {
				error(ctx, aexpr->loc, expr,
					"Invalid result type (dangling or ambiguous null)");
				return;
			}
		}

		struct match_case *_case = expr->match.cases;
		struct ast_match_case *acase = aexpr->match.cases;
		while (_case) {
			if (hint && !type_is_assignable(ctx, hint, _case->value->result)) {
				error(ctx, acase->exprs.expr->loc, expr,
					"Match case is not assignable to result type");
				return;
			}
			_case->value = lower_implicit_cast(ctx, 
				expr->result, _case->value);
			_case = _case->next;
			acase = acase->next;
		}

		struct type_tagged_union *tu = result_type.next;
		while (tu) {
			struct type_tagged_union *next = tu->next;
			free(tu);
			tu = next;
		}
	}
}

static void
check_expr_measure(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->result = &builtin_type_size;
	switch (aexpr->measure.op) {
	case M_ALIGN:
	case M_SIZE:
		break;
	case M_LEN:
		expr->len.value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->measure.value, expr->len.value, NULL);
		const struct type *type = check_autodereference(ctx,
				aexpr->measure.value->loc, expr->len.value->result);
		type = type_dealias(ctx, type);
		enum type_storage vstor = type->storage;
		bool valid = vstor == STORAGE_ARRAY || vstor == STORAGE_SLICE
			|| vstor == STORAGE_STRING || vstor == STORAGE_ERROR;
		if (!valid) {
			char *typename = gen_typename(expr->len.value->result);
			error(ctx, aexpr->measure.value->loc, expr,
				"len argument must be of an array, slice, or str type, but got %s",
				typename);
			free(typename);
			return;
		}
		if (vstor == STORAGE_ARRAY) {
			if (type->array.length == SIZE_UNDEFINED) {
				error(ctx, aexpr->measure.value->loc, expr,
					"Cannot take length of unbounded array type");
				return;
			}
			expr->type = EXPR_LITERAL;
			expr->result = &builtin_type_size;
			expr->literal.object = NULL;
			expr->literal.uval = type->array.length;
			return;
		}
		expr->type = EXPR_LEN;
		return;
	case M_OFFSET:
		expr->type = EXPR_LITERAL;
		if (aexpr->measure.value->type != EXPR_ACCESS) {
			error(ctx, aexpr->measure.value->loc, expr,
				"offset argument must be a field or tuple access");
			return;
		}
		if (aexpr->measure.value->access.type != ACCESS_FIELD
				&& aexpr->measure.value->access.type != ACCESS_TUPLE) {
			error(ctx, aexpr->measure.value->loc, expr,
				"offset argument must be a field or tuple access");
			return;
		}
		struct expression *value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->measure.value, value, NULL);
		if (value->result->storage == STORAGE_ERROR) {
			return;
		}
		if (value->access.type == ACCESS_FIELD) {
			expr->literal.uval = value->access.field->offset;
		} else {
			assert(value->access.type == ACCESS_TUPLE);
			expr->literal.uval = value->access.tvalue->offset;
		}
		return;
	}

	expr->type = EXPR_LITERAL;
	struct errors **cur_err = ctx->next;
	struct dimensions dim = type_store_lookup_dimensions(
		ctx, aexpr->measure.type);
	if (ctx->next != cur_err) {
		mkerror(expr);
		return;
	}
	struct ast_types *next = ctx->unresolved;
	ctx->unresolved = xcalloc(1, sizeof(struct ast_types));
	ctx->unresolved->type = aexpr->measure.type;
	ctx->unresolved->next = next;
	if (aexpr->measure.op == M_ALIGN) {
		if (dim.align == ALIGN_UNDEFINED) {
			error(ctx, aexpr->measure.type->loc, expr,
				"Cannot take alignment of a type with undefined alignment");
			return;
		}
		expr->literal.uval = dim.align;
	} else {
		if (dim.size == SIZE_UNDEFINED) {
			error(ctx, aexpr->measure.type->loc, expr,
				"Cannot take size of a type with undefined size");
			return;
		}
		expr->literal.uval = dim.size;
	}
}

static void
check_expr_propagate(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	struct expression *lvalue = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->propagate.value, lvalue, hint == &builtin_type_void ? NULL : hint);

	const struct type *intype = lvalue->result;
	if (intype->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	if (type_dealias(ctx, intype)->storage != STORAGE_TAGGED) {
		char *typename = gen_typename(intype);
		error(ctx, aexpr->loc, expr,
			"Cannot use error propagation on non-tagged type %s",
			typename);
		free(typename);
		return;
	}
	if (!aexpr->propagate.abort) {
		struct scope *defer = scope_lookup_class(ctx->scope, SCOPE_DEFER);
		if (defer) {
			error(ctx, aexpr->loc, expr,
				"Cannot use error propagation in a defer expression");
			return;
		}
	}

	struct type_tagged_union result_tagged = {0};
	struct type_tagged_union *tagged = &result_tagged,
		**next_tag = &tagged->next;

	struct type_tagged_union return_tagged = {0};
	struct type_tagged_union *rtagged = &return_tagged,
		**next_rtag = &rtagged->next;

	const struct type_tagged_union *intu = &type_dealias(ctx, intype)->tagged;
	for (; intu; intu = intu->next) {
		if (intu->type->flags & TYPE_ERROR) {
			if (rtagged->type) {
				rtagged = *next_rtag =
					xcalloc(1, sizeof(struct type_tagged_union));
				next_rtag = &rtagged->next;
				rtagged->type = intu->type;
			} else {
				rtagged->type = intu->type;
			}
		} else {
			if (tagged->type) {
				tagged = *next_tag =
					xcalloc(1, sizeof(struct type_tagged_union));
				next_tag = &tagged->next;
				tagged->type = intu->type;
			} else {
				tagged->type = intu->type;
			}
		}
	}

	if (!return_tagged.type) {
		error(ctx, aexpr->loc, expr,
			"No error can occur here, cannot propagate");
		return;
	}

	const struct type *return_type;
	if (return_tagged.next) {
		return_type = type_store_lookup_tagged(
			ctx, aexpr->loc, &return_tagged);
	} else {
		return_type = return_tagged.type;
	}

	const struct type *result_type;
	if (!result_tagged.type) {
		result_type = &builtin_type_never;
	} else if (result_tagged.next) {
		result_type = type_store_lookup_tagged(
			ctx, aexpr->loc, &result_tagged);
	} else {
		result_type = result_tagged.type;
	}

	// Lower to a match expression
	expr->type = EXPR_MATCH;
	expr->match.value = lvalue;

	struct scope *scope = scope_push(&ctx->scope, SCOPE_MATCH);
	struct match_case *case_ok = xcalloc(1, sizeof(struct match_case));
	struct match_case *case_err = xcalloc(1, sizeof(struct match_case));

	struct scope_object *ok_obj = NULL, *err_obj = NULL;
	if (result_type->size != SIZE_UNDEFINED) {
		struct ident *id = intern_generated(ctx, "ok.%d");
		ok_obj = scope_insert(scope, O_BIND, id, id, result_type, NULL);
	}

	case_ok->type = result_type;
	case_ok->object = ok_obj;
	case_ok->value = xcalloc(1, sizeof(struct expression));
	case_ok->value->result = result_type;
	case_ok->value->loc = expr->loc;
	if (ok_obj) {
		case_ok->value->type = EXPR_ACCESS;
		case_ok->value->access.type = ACCESS_IDENTIFIER;
		case_ok->value->access.object = ok_obj;
	} else {
		case_ok->value->type = EXPR_LITERAL;
	}

	case_err->value = xcalloc(1, sizeof(struct expression));
	case_err->value->loc = expr->loc;

	if (aexpr->propagate.abort) {
		case_err->value->type = EXPR_ASSERT;
		case_err->value->assert = (struct expression_assert){
			.cond = NULL,
			.message = NULL,
			.fixed_reason = ABORT_PROPAGATE_ERROR_OCCURRED,
		};
	} else {
		if (return_type->size != SIZE_UNDEFINED) {
			struct ident *id = intern_generated(ctx, "err.%d");
			err_obj = scope_insert(scope, O_BIND, id, id, return_type, NULL);
		}
		case_err->type = return_type;
		case_err->object = err_obj;
		if (!type_is_assignable(ctx, ctx->fntype->func.result, return_type)) {
			char *res = gen_typename(ctx->fntype->func.result);
			char *ret = gen_typename(return_type);
			error(ctx, aexpr->loc, expr,
				"Error type %s is not assignable to function result type %s",
				ret, res);
			free(res);
			free(ret);
			return;
		}

		case_err->value->type = EXPR_RETURN;

		struct expression *rval =
			xcalloc(1, sizeof(struct expression));
		rval->result = return_type;
		rval->loc = expr->loc;
		if (err_obj != NULL) {
			rval->type = EXPR_ACCESS;
			rval->access.type = ACCESS_IDENTIFIER;
			rval->access.object = err_obj;
		} else {
			rval->type = EXPR_LITERAL;
		}
		case_err->value->_return.value = lower_implicit_cast(ctx, 
				ctx->fntype->func.result, rval);
	}
	case_err->value->result = &builtin_type_never;

	expr->match.cases = case_ok;
	case_ok->next = case_err;

	scope_pop(&ctx->scope);
	expr->result = result_type;
}

static void
check_expr_return(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	struct scope *defer = scope_lookup_class(ctx->scope, SCOPE_DEFER);
	if (defer) {
		error(ctx, aexpr->loc, NULL,
			"Cannot return inside a defer expression");
		// continue checking so other errors can be reported
	}

	expr->type = EXPR_RETURN;
	expr->result = &builtin_type_never;

	struct expression *rval = expr->_return.value =
		xcalloc(1, sizeof(struct expression));
	if (aexpr->_return.value) {
		const struct type *hint = NULL;
		if (ctx->fntype) {
			hint = ctx->fntype->func.result;
		}
		check_expression(ctx, aexpr->_return.value, rval, hint);
	} else {
		rval->type = EXPR_LITERAL;
		rval->result = &builtin_type_void;
	}
	if (ctx->fntype == NULL) {
		error(ctx, aexpr->loc, NULL, "Cannot return outside a function body");
		return;
	}

	if (!type_is_assignable(ctx, ctx->fntype->func.result, rval->result)) {
		char *rettypename = gen_typename(rval->result);
		char *fntypename = gen_typename(ctx->fntype->func.result);
		error(ctx, aexpr->loc, NULL,
			"Return type %s is not assignable to function result type %s",
			rettypename, fntypename);
		free(rettypename);
		free(fntypename);
		return;
	}
	expr->_return.value = lower_implicit_cast(ctx, ctx->fntype->func.result, rval);
}

static void
slice_bounds_check(struct context *ctx, struct expression *expr)
{
	const struct type *atype = type_dereference(ctx, expr->slice.object->result, false);
	const struct type *dtype = type_dealias(ctx, atype);
	struct expression start, end;
	enum {
		START = 1, END = 1 << 1, LENGTH = 1 << 2
	} bounds = 0;

	if (expr->slice.start && eval_expr(ctx, expr->slice.start, &start)) {
		bounds |= START;
	}
	if (expr->slice.end && eval_expr(ctx, expr->slice.end, &end)) {
		bounds |= END;
	}
	if (dtype->storage == STORAGE_ARRAY && dtype->array.length != SIZE_UNDEFINED) {
		bounds |= LENGTH;
	}

	if ((bounds & (START | LENGTH)) == (START | LENGTH)
			&& start.literal.uval > dtype->array.length) {
		error(ctx, expr->loc, expr,
			"Start index must not be greater than array length");
	}
	if ((bounds & (START | END)) == (START | END)
			&& start.literal.uval > end.literal.uval) {
		error(ctx, expr->loc, expr,
			"Start index must not be greater than end index");
	}
	if ((bounds & (END | LENGTH)) == (END | LENGTH)
			&& end.literal.uval > dtype->array.length) {
		error(ctx, expr->loc, expr,
			"End index must not be greater than array length");
	}
}

static void
check_expr_slice(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_SLICE;

	expr->slice.object = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->slice.object, expr->slice.object, NULL);
	if (expr->slice.object->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}
	const struct type *atype = check_autodereference(ctx,
			aexpr->slice.object->loc, expr->slice.object->result);
	const struct type *dtype = type_dealias(ctx, atype);
	if (dtype->storage != STORAGE_SLICE
			&& dtype->storage != STORAGE_ARRAY) {
		error(ctx, aexpr->slice.object->loc, expr,
			"Cannot slice non-array, non-slice object");
		return;
	}

	const struct type *itype;
	if (aexpr->slice.start) {
		expr->slice.start = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->slice.start, expr->slice.start, &builtin_type_size);
		itype = type_dealias(ctx, expr->slice.start->result);
		if (!type_is_integer(ctx, itype)) {
			error(ctx, aexpr->slice.start->loc, expr,
				"Cannot use non-integer %s type as slicing operand",
				type_storage_unparse(itype->storage));
			return;
		}
		if (dtype->array.members->size == SIZE_UNDEFINED) {
			error(ctx, aexpr->slice.start->loc, expr,
				"Cannot use left subslicing operand on a slice with member type of unknown size");
			return;
		}

		expr->slice.start = lower_implicit_cast(ctx, 
			&builtin_type_size, expr->slice.start);
	}

	if (aexpr->slice.end) {
		expr->slice.end = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, aexpr->slice.end, expr->slice.end, &builtin_type_size);
		itype = type_dealias(ctx, expr->slice.end->result);
		if (!type_is_integer(ctx, itype)) {
			error(ctx, aexpr->slice.end->loc, expr,
				"Cannot use non-integer %s type as slicing operand",
				type_storage_unparse(itype->storage));
			return;
		}
		expr->slice.end = lower_implicit_cast(ctx, 
			&builtin_type_size, expr->slice.end);
	} else if (dtype->storage == STORAGE_ARRAY
			&& dtype->array.length == SIZE_UNDEFINED) {
		error(ctx, aexpr->loc, expr,
			"Must have end index on array of undefined length");
		return;
	}

	slice_bounds_check(ctx, expr);

	if (dtype->storage == STORAGE_SLICE) {
		expr->result = atype;
	} else {
		expr->result = type_store_lookup_slice(ctx, aexpr->loc,
			dtype->array.members);
	}
}

static void
check_struct_exhaustive(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *stype)
{
	stype = type_dealias(ctx, stype);
	if (stype->storage == STORAGE_UNION) {
		return;
	}
	assert(stype->storage == STORAGE_STRUCT);
	struct struct_field *sf = stype->struct_union.fields;
	struct ast_field_value *af = aexpr->_struct.fields;

	// XXX: O(n^2)?
	while (sf) {
		bool found = false;
		for (struct ast_field_value *f = af; f;
				f = f->next) {
			if (!sf->name) {
				check_struct_exhaustive(ctx, aexpr, expr,
					sf->type);
				found = true;
				continue;
			}
			if (strcmp(f->name, sf->name) == 0) {
				if (found) {
					error(ctx, aexpr->loc, expr,
						"Field '%s' is initialized multiple times",
						sf->name);
				}
				found = true;
			}
		}

		if (!found && (!aexpr->_struct.autofill
					|| !type_has_default(ctx, sf->type))) {
			error(ctx, aexpr->loc, expr,
				"Field '%s' is uninitialized",
				sf->name);
		}

		sf = sf->next;
	}
}

static void
check_expr_struct(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_STRUCT;

	const struct type *stype = NULL;
	if (aexpr->_struct.type != NULL) {
		struct scope_object *obj = scope_lookup(ctx->scope, aexpr->_struct.type);
		// resolve the unknown type
		wrap_resolver(ctx, obj, resolve_type);
		if (!obj) {
			error(ctx, aexpr->loc, expr,
				"Unknown type alias");
			return;
		}

		if (obj->otype != O_TYPE) {
			error(ctx, aexpr->loc, expr,
					"Identifier does not refer to a type");
			return;
		}
		stype = obj->type;
		enum type_storage storage = type_dealias(ctx, stype)->storage;
		if (storage != STORAGE_STRUCT && storage != STORAGE_UNION) {
			error(ctx, aexpr->loc, expr,
				"Type named is not a struct or union type");
			return;
		}
	}

	struct ast_type satype = {
		.storage = STORAGE_STRUCT,
	};
	struct ast_struct_union_field *tfield = &satype.struct_union.fields;
	struct ast_struct_union_field **tnext = &tfield->next;
	struct expr_struct_field *sexpr, **snext = &expr->_struct.fields;
	expr->_struct.autofill = aexpr->_struct.autofill;
	if (stype == NULL && expr->_struct.autofill) {
		error(ctx, aexpr->loc, expr,
				"Autofill is only permitted for named struct initializers");
		return;
	}

	struct ast_field_value *afield = aexpr->_struct.fields;
	while (afield) {
		const struct type *ftype;
		*snext = sexpr = xcalloc(1, sizeof(struct expr_struct_field));
		snext = &sexpr->next;
		sexpr->value = xcalloc(1, sizeof(struct expression));
		if (!stype) {
			assert(afield->name); // TODO
			if (!afield->type) {
				error(ctx, aexpr->loc, expr,
					"Unnamed struct must specify field type");
				return;
			}
			tfield->name = afield->name;
			tfield->type = afield->type;
			ftype = type_store_lookup_atype(ctx, tfield->type);
			check_expression(ctx, afield->initializer,
				sexpr->value, ftype);
			if (afield->next) {
				*tnext = tfield = xcalloc(
					1, sizeof(struct ast_struct_union_type));
				tnext = &tfield->next;
			}
		} else {
			if (!afield->name) {
				error(ctx, afield->initializer->loc, expr,
					"Cannot embed a struct literal into "
					"a named struct literal");
				return;
			}
			sexpr->field = type_get_field(ctx, type_dealias(ctx, stype),
					afield->name);
			if (!sexpr->field) {
				error(ctx, afield->initializer->loc, expr,
					"No field by this name exists for this type");
				return;
			}
			ftype = sexpr->field->type;
			check_expression(ctx, afield->initializer,
					sexpr->value, ftype);

			if (!type_is_assignable(ctx, sexpr->field->type, sexpr->value->result)) {
				error(ctx, afield->initializer->loc, expr,
					"Initializer is not assignable to struct field");
				return;
			}
			sexpr->value = lower_implicit_cast(ctx, 
				sexpr->field->type, sexpr->value);
		}

		afield = afield->next;
	}

	if (stype) {
		expr->result = stype;
		check_struct_exhaustive(ctx, aexpr, expr, stype);
	} else {
		expr->result = type_store_lookup_atype(ctx, &satype);

		tfield = &satype.struct_union.fields;
		sexpr = expr->_struct.fields;
		while (tfield) {
			const struct struct_field *field = type_get_field(ctx, 
				expr->result, tfield->name);
			if (!field) {
				// TODO: Use more specific error location
				error(ctx, aexpr->loc, expr,
					"No field by this name exists for this type");
				return;
			}
			if (!type_is_assignable(ctx, field->type, sexpr->value->result)) {
				error(ctx, aexpr->loc, expr,
					"Cannot initialize struct field '%s' from value of this type",
					field->name);
				return;
			}
			sexpr->field = field;
			sexpr->value = lower_implicit_cast(ctx, field->type, sexpr->value);

			struct ast_struct_union_field *next = tfield->next;
			if (tfield != &satype.struct_union.fields) {
				free(tfield);
			}
			tfield = next;
			sexpr = sexpr->next;
		}
	}
}

static int
casecmp(const void *_a, const void *_b)
{
	const struct expression *a = *(const struct expression **)_a;
	const struct expression *b = *(const struct expression **)_b;
	assert(a->type == EXPR_LITERAL && b->type == EXPR_LITERAL);
	assert(type_dealias(NULL, a->result)->storage
		== type_dealias(NULL, b->result)->storage);
	if (type_is_signed(NULL, a->result)) {
		return a->literal.ival < b->literal.ival ? -1
			: a->literal.ival > b->literal.ival ? 1 : 0;
	} else if (type_is_integer(NULL, a->result)) {
		return a->literal.uval < b->literal.uval ? -1
			: a->literal.uval > b->literal.uval ? 1 : 0;
	} else if (type_dealias(NULL, a->result)->storage == STORAGE_STRING) {
		size_t len = a->literal.string.len < b->literal.string.len
			? a->literal.string.len : b->literal.string.len;
		int ret = memcmp(a->literal.string.value,
			b->literal.string.value, len);
		if (ret != 0) {
			return ret;
		}
		return a->literal.string.len < b->literal.string.len ? -1
			: a->literal.string.len > b->literal.string.len ? 1 : 0;
	} else if (type_dealias(NULL, a->result)->storage == STORAGE_BOOL) {
		return (int)a->literal.bval - (int)b->literal.bval;
	} else {
		assert(type_dealias(NULL, a->result)->storage == STORAGE_RCONST
			|| type_dealias(NULL, a->result)->storage == STORAGE_RUNE);
		return a->literal.rune < b->literal.rune ? -1
			: a->literal.rune > b->literal.rune ? 1 : 0;
	}
}

static size_t
num_cases(struct context *ctx, const struct type *type)
{
	type = type_dealias(ctx, type);
	switch (type->storage) {
	case STORAGE_BOOL:
		return 2;
	case STORAGE_STRING:
		return -1;
	case STORAGE_ENUM:;
		struct scope_object *obj = type->_enum.values->objects;
		assert(obj != NULL);
		size_t n = 0;
		for (struct scope_object *o = obj; o; o = o->lnext, ++n) {
			if (o->otype == O_SCAN) {
				wrap_resolver(ctx, o, resolve_enum_field);
			}
			assert(o->otype == O_CONST);
		}
		struct expression **cases_array =
			xcalloc(n, sizeof(struct expression *));
		size_t i = 0;
		for (struct scope_object *o = obj; o; o = o->lnext, ++i) {
			cases_array[i] = o->value;
		}
		qsort(cases_array, n, sizeof(struct expression *), &casecmp);
		for (size_t i = 1; i < n; ++i) {
			if (casecmp(&cases_array[i - 1], &cases_array[i]) == 0) {
				--n;
			}
		}
		free(cases_array);
		return n;
	default:
		assert(type_is_integer(ctx, type)
			|| type->storage == STORAGE_RUNE);
		assert(!type_is_flexible(type));
		if (type->size >= sizeof(size_t)) {
			return -1;
		}
		return (size_t)1 << (type->size * 8);
	}
}

static void
check_expr_switch(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_SWITCH;

	struct expression *value = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->_switch.value, value, NULL);
	const struct type *type = lower_flexible(ctx, value->result, NULL);
	expr->_switch.value = value;
	if (!type_is_integer(ctx, type)
			&& type_dealias(ctx, type)->storage != STORAGE_STRING
			&& type_dealias(ctx, type)->storage != STORAGE_BOOL
			&& type_dealias(ctx, type)->storage != STORAGE_RUNE) {
		error(ctx, aexpr->loc, expr,
			"Cannot switch on %s type",
			type_storage_unparse(type_dealias(ctx, type)->storage));
		return;
	}

	struct type_tagged_union *tagged = NULL, *result = NULL;

	struct switch_case **next = &expr->_switch.cases, *_case = NULL;
	size_t n = 0;
	bool has_default_case = false;
	struct ast_switch_case *acase;
	for (acase = aexpr->_switch.cases; acase; acase = acase->next) {
		_case = *next = xcalloc(1, sizeof(struct switch_case));
		next = &_case->next;

		_case->value = xcalloc(1, sizeof(struct expression));

		if (acase->options == NULL) {
			if (has_default_case) {
				error(ctx, acase->exprs.expr->loc, _case->value,
					"Duplicate default case");
			}
			has_default_case = true;
		}

		struct case_option *opt, **next_opt = &_case->options;
		for (const struct ast_case_option *aopt = acase->options;
				aopt; aopt = aopt->next) {
			opt = *next_opt = xcalloc(1, sizeof(struct case_option));
			struct expression *value =
				xcalloc(1, sizeof(struct expression));
			struct expression *evaled =
				xcalloc(1, sizeof(struct expression));

			check_expression(ctx, aopt->value, value, type);
			if (!type_is_assignable(ctx, type, value->result)) {
				error(ctx, aopt->value->loc, expr,
					"Invalid type for switch case");
				return;
			}
			value = lower_implicit_cast(ctx, type, value);

			if (!eval_expr(ctx, value, evaled)) {
				error(ctx, aopt->value->loc, expr,
					"Unable to evaluate case at compile time");
				return;
			}

			opt->value = evaled;
			next_opt = &opt->next;
			n++;
		}

		// Lower to compound
		// TODO: This should probably be done in a more first-class way
		struct ast_expression compound = {
			.type = EXPR_COMPOUND,
			.compound = {
				.label = aexpr->_switch.label,
				.list = acase->exprs,
			},
		};
		check_expression(ctx, &compound, _case->value, hint);
		if (tagged == NULL) {
			result = tagged = xcalloc(1, sizeof *tagged);
		} else if (tagged->type && tagged->type != _case->value->result) {
			tagged = tagged->next = xcalloc(1, sizeof *tagged);
		}
		tagged->type = _case->value->result;
	}

	struct expression **cases_array = xcalloc(n, sizeof(struct expression *));
	size_t i = 0;
	for (_case = expr->_switch.cases; _case; _case = _case->next) {
		for (const struct case_option *opt = _case->options;
				opt; opt = opt->next) {
			assert(i < n);
			if (opt->value->result->storage != STORAGE_ERROR) {
				cases_array[i] = opt->value;
				i++;
			}
		}
	}
	n = i;
	qsort(cases_array, n, sizeof(struct expression *), &casecmp);
	bool has_duplicate = false;
	for (size_t i = 1; i < n; i++) {
		if (casecmp(&cases_array[i - 1], &cases_array[i]) == 0) {
			error(ctx, cases_array[i - 1]->loc, cases_array[i - 1],
				"Duplicate switch case");
			has_duplicate = true;
		}
	}
	free(cases_array);
	if (!has_default_case && !has_duplicate
			&& value->result->storage != STORAGE_ERROR
			&& (n == (size_t)-1 || n != num_cases(ctx, value->result))) {
		error(ctx, aexpr->loc, value,
			"Switch expression isn't exhaustive");
	}

	if (hint) {
		expr->result = hint;
	} else {
		expr->result = type_store_reduce_result(
			ctx, aexpr->loc, result);
		if (expr->result == NULL) {
			error(ctx, aexpr->loc, expr,
				"Invalid result type (dangling or ambiguous null)");
			return;
		}
	}

	_case = expr->_switch.cases;
	acase = aexpr->_switch.cases;
	while (_case) {
		if (!type_is_assignable(ctx, expr->result, _case->value->result)) {
			error(ctx, acase->exprs.expr->loc, expr,
				"Switch case is not assignable to result type");
			return;
		}
		_case->value = lower_implicit_cast(ctx,
			expr->result, _case->value);
		_case = _case->next;
		acase = acase->next;
	}

	while (result) {
		struct type_tagged_union *next = result->next;
		free(result);
		result = next;
	}
}

static void
check_expr_tuple(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_TUPLE;

	const struct type_tuple *ttuple = NULL;
	if (hint && type_dealias(ctx, hint)->storage == STORAGE_TUPLE) {
		ttuple = &type_dealias(ctx, hint)->tuple;
	}

	struct type_tuple result = {0};
	struct type_tuple *rtype = &result;

	struct expression_tuple *tuple = &expr->tuple;
	for (const struct ast_expression_tuple *atuple = &aexpr->tuple;
			atuple; atuple = atuple->next) {
		tuple->value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, atuple->expr, tuple->value, ttuple ? ttuple->type : NULL);
		rtype->type = tuple->value->result;

		if (atuple->next) {
			rtype->next = xcalloc(1, sizeof(struct type_tuple));
			rtype = rtype->next;
			tuple->next = xcalloc(1, sizeof(struct expression_tuple));
			tuple = tuple->next;
		}

		if (ttuple) {
			ttuple = ttuple->next;
		}
	}

	if (hint && type_dealias(ctx, hint)->storage == STORAGE_TUPLE) {
		expr->result = hint;
	} else if (hint && type_dealias(ctx, hint)->storage == STORAGE_TAGGED) {
		for (const struct type_tagged_union *tu =
				&type_dealias(ctx, hint)->tagged;
				tu; tu = tu->next) {
			if (type_dealias(ctx, tu->type)->storage != STORAGE_TUPLE) {
				continue;
			}
			const struct type_tuple *ttuple =
				&type_dealias(ctx, tu->type)->tuple;
			const struct expression_tuple *etuple = &expr->tuple;
			bool valid = true;
			while (etuple) {
				if (!ttuple || !type_is_assignable(ctx, ttuple->type,
						etuple->value->result)) {
					valid = false;
					break;
				}
				ttuple = ttuple->next;
				etuple = etuple->next;
			}
			if (!ttuple && valid) {
				expr->result = type_dealias(ctx, tu->type);
				break;
			}
		}
		if (!expr->result) {
			error(ctx, aexpr->loc, expr,
				"Tuple value is not assignable to tagged union hint");
			return;
		}
	} else {
		expr->result = type_store_lookup_tuple(ctx, aexpr->loc, &result);
		if (expr->result == &builtin_type_error) {
			// an error occurred
			return;
		}
	}

	ttuple = &type_dealias(ctx, expr->result)->tuple;
	struct expression_tuple *etuple = &expr->tuple;
	const struct ast_expression_tuple *atuple = &aexpr->tuple;
	while (etuple) {
		if (!ttuple) {
			error(ctx, atuple->expr->loc, expr,
				"Too many values for tuple type");
			return;
		}
		if (!type_is_assignable(ctx, ttuple->type, etuple->value->result)) {
			error(ctx, atuple->expr->loc, expr,
				"Value is not assignable to tuple value type");
			return;
		}
		etuple->value = lower_implicit_cast(ctx, ttuple->type, etuple->value);
		etuple = etuple->next;
		atuple = atuple->next;
		ttuple = ttuple->next;
	}
	if (ttuple) {
		error(ctx, aexpr->loc, expr,
			"Too few values for tuple type");
		return;
	}
}

static void
check_expr_unarithm(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_UNARITHM;

	struct expression *operand = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->unarithm.operand, operand, NULL);
	expr->unarithm.operand = operand;
	expr->unarithm.op = aexpr->unarithm.op;
	if (operand->result->storage == STORAGE_ERROR) {
		mkerror(expr);
		return;
	}

	switch (expr->unarithm.op) {
	case UN_LNOT:
		if (type_dealias(ctx, operand->result)->storage != STORAGE_BOOL) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot perform logical NOT (!) on non-boolean type");
			return;
		}
		expr->result = &builtin_type_bool;
		break;
	case UN_BNOT:
		if (!type_is_integer(ctx, operand->result)) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot perform binary NOT (~) on non-integer type");
			return;
		}
		expr->result = operand->result;
		break;
	case UN_MINUS:
		if (!type_is_numeric(ctx, operand->result)) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot perform operation on non-numeric type");
			return;
		}
		if (operand->result->storage == STORAGE_ICONST) {
			// Not technically quite right, but we need
			// operand->result to be lowered with expr->result, and
			// this is correct enough
			const struct type *old = operand->result;
			const struct type *new = type_create_flexible(
				STORAGE_ICONST, -old->flexible.min,
				-old->flexible.max);
			lower_flexible(ctx, old, new);
		}
		expr->result = operand->result;
		break;
	case UN_ADDRESS:;
		const struct type *ptrhint = NULL;
		if (hint && type_dealias(ctx, hint)->storage == STORAGE_POINTER) {
			ptrhint = type_dealias(ctx, hint)->pointer.referent;
			if (type_dealias(ctx, ptrhint)->storage == STORAGE_OPAQUE) {
				ptrhint = NULL;
			}
		}
		if (type_is_flexible(operand->result) && ptrhint) {
			const struct type *promoted =
				promote_flexible(ctx, operand->result, ptrhint);
			if (promoted) {
				operand->result = promoted;
			}
		} else if (ptrhint) {
			uint32_t result_id = type_dealias(ctx, operand->result)->id;
			uint32_t ptrhint_id = type_dealias(ctx, ptrhint)->id;
			if (result_id == ptrhint_id) {
				operand->result = ptrhint;
			}
		}
		expr->result = type_store_lookup_pointer(
			ctx, aexpr->loc, operand->result, false);
		break;
	case UN_DEREF:
		if (type_dealias(ctx, operand->result)->storage != STORAGE_POINTER) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot de-reference non-pointer type");
			return;
		}
		if (type_dealias(ctx, operand->result)->pointer.nullable) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot dereference nullable pointer type");
			return;
		}
		if (type_dealias(ctx, operand->result)->pointer.referent->size
				== SIZE_UNDEFINED) {
			error(ctx, aexpr->unarithm.operand->loc, expr,
				"Cannot dereference pointer to type of undefined size");
			return;
		}
		expr->result = type_dealias(ctx, operand->result)->pointer.referent;
		break;
	}
}

static void
check_expr_vastart(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	if (ctx->fntype->func.variadism != VARIADISM_C) {
		error(ctx, aexpr->loc, expr,
			"Cannot use vastart within function which does not use C-style variadism");
		return;
	}
	expr->type = EXPR_VASTART;
	expr->result = &builtin_type_valist;
}

static void
check_expr_vaarg(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_VAARG;
	expr->vaarg.ap = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->vaarg.ap, expr->vaarg.ap, &builtin_type_valist);
	if (type_dealias(ctx, expr->vaarg.ap->result)->storage != STORAGE_VALIST) {
		error(ctx, aexpr->loc, expr,
			"Expected vaarg operand to be valist");
		return;
	}
	expr->result = type_store_lookup_atype(ctx, aexpr->vaarg.type);
	if (expr->result->size == SIZE_UNDEFINED) {
		error(ctx, aexpr->loc, expr, "vaarg type must have defined size");
		return;
	}
}

static void
check_expr_vaend(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->type = EXPR_VAEND;
	expr->vaarg.ap = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aexpr->vaarg.ap, expr->vaarg.ap, &builtin_type_valist);
	if (type_dealias(ctx, expr->vaarg.ap->result)->storage != STORAGE_VALIST) {
		error(ctx, aexpr->loc, expr,
			"Expected vaend operand to be valist");
		return;
	}
	expr->result = &builtin_type_void;
}

void
check_expression(struct context *ctx,
	const struct ast_expression *aexpr,
	struct expression *expr,
	const struct type *hint)
{
	expr->loc = aexpr->loc;

	switch (aexpr->type) {
	case EXPR_ACCESS:
		check_expr_access(ctx, aexpr, expr, hint);
		break;
	case EXPR_ALLOC:
		check_expr_alloc(ctx, aexpr, expr, hint);
		break;
	case EXPR_APPEND:
		check_expr_append_insert(ctx, aexpr, expr, hint);
		break;
	case EXPR_ASSERT:
		check_expr_assert(ctx, aexpr, expr, hint);
		break;
	case EXPR_ASSIGN:
		check_expr_assign(ctx, aexpr, expr, hint);
		break;
	case EXPR_BINARITHM:
		check_expr_binarithm(ctx, aexpr, expr, hint);
		break;
	case EXPR_BINDING:
	case EXPR_DEFINE:
		check_expr_binding(ctx, aexpr, expr, hint);
		break;
	case EXPR_BREAK:
	case EXPR_CONTINUE:
	case EXPR_YIELD:
		check_expr_control(ctx, aexpr, expr, hint);
		break;
	case EXPR_CALL:
		check_expr_call(ctx, aexpr, expr, hint);
		break;
	case EXPR_CAST:
		check_expr_cast(ctx, aexpr, expr, hint);
		break;
	case EXPR_COMPOUND:
		check_expr_compound(ctx, aexpr, expr, hint);
		break;
	case EXPR_LITERAL:
		check_expr_literal(ctx, aexpr, expr, hint);
		break;
	case EXPR_DEFER:
		check_expr_defer(ctx, aexpr, expr, hint);
		break;
	case EXPR_DELETE:
		check_expr_delete(ctx, aexpr, expr, hint);
		break;
	case EXPR_FOR:
		check_expr_for(ctx, aexpr, expr, hint);
		break;
	case EXPR_FREE:
		check_expr_free(ctx, aexpr, expr, hint);
		break;
	case EXPR_IF:
		check_expr_if(ctx, aexpr, expr, hint);
		break;
	case EXPR_INSERT:
		check_expr_append_insert(ctx, aexpr, expr, hint);
		break;
	case EXPR_MATCH:
		check_expr_match(ctx, aexpr, expr, hint);
		break;
	case EXPR_MEASURE:
		check_expr_measure(ctx, aexpr, expr, hint);
		break;
	case EXPR_PROPAGATE:
		check_expr_propagate(ctx, aexpr, expr, hint);
		break;
	case EXPR_RETURN:
		check_expr_return(ctx, aexpr, expr, hint);
		break;
	case EXPR_SLICE:
		check_expr_slice(ctx, aexpr, expr, hint);
		break;
	case EXPR_STRUCT:
		check_expr_struct(ctx, aexpr, expr, hint);
		break;
	case EXPR_SWITCH:
		check_expr_switch(ctx, aexpr, expr, hint);
		break;
	case EXPR_TUPLE:
		check_expr_tuple(ctx, aexpr, expr, hint);
		break;
	case EXPR_UNARITHM:
		check_expr_unarithm(ctx, aexpr, expr, hint);
		break;
	case EXPR_VAARG:
		check_expr_vaarg(ctx, aexpr, expr, hint);
		break;
	case EXPR_VAEND:
		check_expr_vaend(ctx, aexpr, expr, hint);
		break;
	case EXPR_VASTART:
		check_expr_vastart(ctx, aexpr, expr, hint);
		break;
	}
	assert(expr->result);
	flexible_refer(expr->result, &expr->result);
}

void
append_decl(struct context *ctx, struct declaration *decl)
{
	struct declarations *decls = xcalloc(1, sizeof(struct declarations));
	decls->decl = *decl;
	decls->next = ctx->decls;
	ctx->decls = decls;
}

static void
resolve_unresolved(struct context *ctx)
{
	while (ctx->unresolved) {
		struct ast_types *unresolved = ctx->unresolved;
		ctx->unresolved = unresolved->next;
		type_store_lookup_atype(ctx, unresolved->type);
		free(unresolved);
	}
}

static void
check_function(struct context *ctx,
	const struct scope_object *obj,
	const struct ast_decl *adecl)
{
	const struct ast_function_decl *afndecl = &adecl->function;
	ctx->fntype = obj->type;
	if (ctx->fntype->storage == STORAGE_ERROR) {
		return;
	}

	struct declaration _decl, *decl = &_decl;
	decl->decl_type = DECL_FUNC;
	decl->func.type = obj->type;
	decl->func.flags = afndecl->flags;
	decl->exported = adecl->exported;
	decl->file = adecl->loc.file;

	decl->symbol = ident_to_sym(ctx->itbl, obj->ident);
	decl->ident = mkident(ctx, afndecl->ident, NULL);

	if (!adecl->function.body) {
		if (decl->func.flags != 0) {
			error(ctx, adecl->loc, NULL,
				"Function attributes cannot be used on prototypes");
			return;
		}
		decl->func.body = NULL;
		goto end; // Prototype
	}
	if (afndecl->symbol != NULL && decl->func.flags != 0) {
		error(ctx, adecl->loc, NULL,
			"@symbol cannot be used alongside other function attributes");
	}

	decl->func.scope = scope_push(&ctx->scope, SCOPE_FUNC);
	struct ast_function_parameters *params = afndecl->prototype.params;
	while (params) {
		const struct type *type = type_store_lookup_atype(
				ctx, params->type);
		if (obj->type->func.variadism == VARIADISM_HARE
				&& !params->next) {
			type = type_store_lookup_slice(ctx, params->loc, type);
		}
		scope_insert(decl->func.scope, O_BIND, params->name,
				params->name, type, NULL);
		params = params->next;
	}

	// TODO: Add function name to errors
	if (decl->func.flags != 0) {
		const char *flag = NULL;
		switch (decl->func.flags) {
		case FN_INIT:
			flag = "@init";
			break;
		case FN_FINI:
			flag = "@fini";
			break;
		case FN_TEST:
			flag = "@test";
			break;
		default:
			error(ctx, adecl->loc, NULL,
				"Only one of @init, @fini, or @test may be used in a function declaration");
			break;
		}
		if (obj->type->func.result != &builtin_type_void) {
			error(ctx, adecl->loc, NULL, "%s function must return void", flag);
		}
		if (decl->exported) {
			error(ctx, adecl->loc, NULL, "%s function cannot be exported", flag);
		}
		if (afndecl->prototype.params) {
			error(ctx, adecl->loc, NULL, "%s function cannot have parameters", flag);
		} else if (obj->type->func.variadism != VARIADISM_NONE) {
			error(ctx, adecl->loc, NULL, "%s function cannot be variadic", flag);
		}
	}

	struct expression *body = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, afndecl->body, body, obj->type->func.result);
	resolve_unresolved(ctx);

	if (!type_is_assignable(ctx, obj->type->func.result, body->result)) {
		char *restypename = gen_typename(body->result);
		char *fntypename = gen_typename(obj->type->func.result);
		error(ctx, afndecl->body->loc, body,
			"Expression result type %s is not assignable to function result type %s",
			restypename, fntypename);
		free(restypename);
		free(fntypename);
		return;
	}

	if (obj->type->func.result->storage != STORAGE_NEVER &&
			obj->type->func.result->size == SIZE_UNDEFINED) {
		char *fntypename = gen_typename(obj->type->func.result);
		error(ctx, afndecl->body->loc, body,
			"Types with undefined size such as %s cannot be returned, consider using a pointer instead",
			fntypename);
		free(fntypename);
		return;
	}
	decl->func.body = lower_implicit_cast(ctx, obj->type->func.result, body);

	scope_pop(&ctx->scope);
	ctx->fntype = NULL;
end:
	if ((adecl->function.flags & FN_TEST) && !ctx->is_test) {
		return;
	}
	append_decl(ctx, decl);
}

static struct scope_object *
incomplete_decl_create(struct context *ctx, struct location loc,
		struct scope *scope, struct ident *ident, struct ident *name)
{
	struct scope *subunit = ctx->unit->parent;
	ctx->unit->parent = NULL;
	struct scope_object *obj = scope_lookup(scope, name);
	ctx->unit->parent = subunit;

	if (obj) {
		error_norec(ctx, loc, "Duplicate global ident '%s'",
			ident_unparse(ident));
	}
	obj = scope_insert(scope, O_SCAN, ident, name, NULL, NULL);
	obj->idecl = xcalloc(1, sizeof(struct incomplete_decl));
	return obj;
}

static void
scan_enum_field(struct context *ctx, struct scope *imports,
		struct scope *enum_scope, const struct type *etype,
		struct ast_enum_field *f)
{
	// We have to process the last field first
	// This way, objects in enum_scope will have lnext pointing to
	// the previous element, which is important for implicit enum values.
	if (f->next) {
		scan_enum_field(ctx, imports, enum_scope, etype, f->next);
	}
	assert(etype->storage == STORAGE_ENUM);
	struct incomplete_enum_field *field =
		xcalloc(1, sizeof(struct incomplete_enum_field));
	*field = (struct incomplete_enum_field){
		.field = f,
		.enum_scope = enum_scope,
	};

	struct ident *name = intern_ident(ctx->itbl, f->name->name, etype->alias.name);
	struct scope_object *obj = incomplete_decl_create(
			ctx, f->loc, enum_scope, name, f->name);
	obj->idecl->type = IDECL_ENUM_FLD;
	obj->idecl->imports = imports;
	obj->type = etype,
	obj->idecl->field = field;
}

static void
check_hosted_main(struct context *ctx,
	struct location loc,
	const struct ast_decl *decl,
	struct ident *ident,
	const char *symbol)
{
	if (*ctx->mainsym == '\0' || ctx->is_test) {
		return;
	}
	if (symbol != ctx->mainsym && (symbol != NULL || ident != ctx->mainident)) {
		return;
	}

	const struct ast_function_decl *func;
	if (decl && decl->decl_type == ADECL_FUNC) {
		func = &decl->function;
		if (func->flags != 0) {
			return;
		}
	} else {
		error(ctx, loc, NULL,
			"main must be a function in hosted environment");
		return;
	}

	if (func->body != NULL && !decl->exported) {
		error(ctx, loc, NULL,
			"main must be exported in hosted environment");
		return;
	}
	if (func->prototype.params != NULL) {
		error(ctx, loc, NULL,
			"main must not have parameters in hosted environment");
		return;
	}
	if (func->prototype.variadism != VARIADISM_NONE) {
		error(ctx, loc, NULL,
			"main must not be variadic in hosted environment");
		return;
	}
	if (func->prototype.result->storage != STORAGE_VOID) {
		error(ctx, loc, NULL,
			"main must return void in hosted environment");
		return;
	}
}

static void
scan_types(struct context *ctx, struct scope *imp, const struct ast_decl *decl)
{
	for (const struct ast_type_decl *t = &decl->type; t; t = t->next) {
		struct ident *with_ns = mkident(ctx,  t->ident, NULL);
		check_hosted_main(ctx, decl->loc, NULL, with_ns, NULL);
		struct scope_object *obj = incomplete_decl_create(ctx,
				decl->loc, ctx->scope, with_ns, t->ident);
		obj->idecl->decl = (struct ast_decl){
			.decl_type = ADECL_TYPE,
			.loc = decl->loc,
			.type = *t,
			.exported = decl->exported,
		};
		obj->idecl->imports = imp;
		if (t->type->storage == STORAGE_ENUM) {
			bool exported = obj->idecl->decl.exported;
			const struct type *type = type_store_lookup_enum(
					ctx, t->type, exported);
			if (type->storage == STORAGE_ERROR) {
				return; // error occured
			}
			scope_push((struct scope **)&type->_enum.values, SCOPE_ENUM);
			scan_enum_field(ctx, imp,
				type->_enum.values, type, t->type->_enum.values);
			type->_enum.values->parent = ctx->defines;
			obj->otype = O_TYPE;
			obj->type = type;
			append_decl(ctx, &(struct declaration){
				.decl_type = DECL_TYPE,
				.file = decl->loc.file,
				.ident = obj->ident,
				.exported = exported,
				.type = type,
			});
		} else {
			obj->idecl->type = IDECL_DECL;
		}
	}
}

static void
unexported_type_error(struct context *ctx,
	struct location loc, const struct type *type)
{
	char *s = gen_typename(type);
	error(ctx, loc, NULL,
		"Can't use unexported type %s in exported declaration", s);
	free(s);
}

static void
check_exported_type(struct context *ctx,
	struct location loc,
	const struct type *type)
{
	switch (type->storage) {
	case STORAGE_ALIAS:
	case STORAGE_ENUM:
		if (!type->alias.exported) {
			unexported_type_error(ctx, loc, type);
		}
		break;
	case STORAGE_ARRAY:
	case STORAGE_SLICE:
		check_exported_type(ctx, loc, type->array.members);
		break;
	case STORAGE_FUNCTION:
		for (const struct type_func_param *param = type->func.params;
				param; param = param->next) {
			check_exported_type(ctx, loc, param->type);
		}
		check_exported_type(ctx, loc, type->func.result);
		break;
	case STORAGE_POINTER:
		check_exported_type(ctx, loc, type->pointer.referent);
		break;
	case STORAGE_STRUCT:
	case STORAGE_UNION:
		for (const struct struct_field *field = type->struct_union.fields;
				field; field = field->next) {
			check_exported_type(ctx, loc, field->type);
		}
		break;
	case STORAGE_TAGGED:
		for (const struct type_tagged_union *t = &type->tagged;
				t; t = t->next) {
			check_exported_type(ctx, loc, t->type);
		}
		break;
	case STORAGE_TUPLE:
		for (const struct type_tuple *t = &type->tuple; t; t = t->next) {
			check_exported_type(ctx, loc, t->type);
		}
		break;
	case STORAGE_BOOL:
	case STORAGE_DONE:
	case STORAGE_ERROR:
	case STORAGE_F32:
	case STORAGE_F64:
	case STORAGE_FCONST:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_I8:
	case STORAGE_ICONST:
	case STORAGE_INT:
	case STORAGE_NEVER:
	case STORAGE_NOMEM:
	case STORAGE_NULL:
	case STORAGE_OPAQUE:
	case STORAGE_RCONST:
	case STORAGE_RUNE:
	case STORAGE_SIZE:
	case STORAGE_STRING:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_U8:
	case STORAGE_UINT:
	case STORAGE_UINTPTR:
	case STORAGE_VALIST:
	case STORAGE_VOID:
		break;
	}
}

static void
resolve_const(struct context *ctx, struct scope_object *obj)
{
	const struct ast_global_decl *decl = &obj->idecl->decl.constant;

	assert(!decl->symbol); // Invariant

	const struct type *type = NULL;
	if (decl->type) {
		type = type_store_lookup_atype(ctx, decl->type);
	}
	struct expression *init = xcalloc(1, sizeof(struct expression));
	obj->value = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, decl->init, init, type);
	if (!decl->type) {
		type = init->result;
		if (type->storage == STORAGE_NULL) {
			error(ctx, decl->init->loc, obj->value,
				"Null is not a valid type for a constant");
			type = &builtin_type_error;
			goto end;
		}
	}
	if (obj->idecl->decl.exported) {
		struct location loc =
			decl->type ? decl->type->loc : decl->init->loc;
		check_exported_type(ctx, loc, type);
	}
	if (!type_is_assignable(ctx, type, init->result)) {
		char *typename1 = gen_typename(init->result);
		char *typename2 = gen_typename(type);
		error(ctx, decl->init->loc, obj->value,
			"Initializer type %s is not assignable to constant type %s",
			typename1, typename2);
		free(typename1);
		free(typename2);
		type = &builtin_type_error;
		goto end;
	}
	if (decl->type) {
		if (decl->type->storage == STORAGE_ARRAY
				&& decl->type->array.contextual) {
			type = lower_flexible(ctx, init->result, NULL);
		} else {
			init = lower_implicit_cast(ctx, type, init);
		}
	}

	if (!eval_expr(ctx, init, obj->value)) {
		error(ctx, decl->init->loc, obj->value,
			"Unable to evaluate initializer at compile time");
		type = &builtin_type_error;
		goto end;
	}
end:
	obj->otype = O_CONST;

	if (!ctx->defines || ctx->errors) {
		return;
	}
	struct scope_object *shadow_obj = scope_lookup(ctx->defines, obj->ident);
	if (shadow_obj && obj != shadow_obj) {
		// Shadowed by define
		if (type_is_flexible(obj->value->result)
				|| type_is_flexible(shadow_obj->value->result)) {
			const struct type *promoted = promote_flexible(ctx,
				obj->value->result, shadow_obj->value->result);
			if (promoted == NULL) {
				const char *msg;
				char *typename = NULL;
				if (!type_is_flexible(obj->value->result)) {
					msg = "Constant of type %s is shadowed by define of incompatible flexible type";
					typename = gen_typename(obj->value->result);
				} else if (!type_is_flexible(shadow_obj->value->result)) {
					msg = "Constant of flexible type is shadowed by define of incompatible type %s";
					typename = gen_typename(shadow_obj->value->result);
				} else {
					msg = "Constant of flexible type is shadowed by define of incompatible flexible type";
				}
				error(ctx, obj->idecl->decl.loc, NULL, msg, typename);
				free(typename);
			} else {
				shadow_obj->value = lower_implicit_cast(ctx,
					promoted, shadow_obj->value);
			}
		} else if (obj->value->result != shadow_obj->value->result) {
			char *typename = gen_typename(obj->value->result);
			char *shadow_typename = gen_typename(shadow_obj->value->result);
			error(ctx, obj->idecl->decl.loc, NULL,
					"Constant of type %s is shadowed by define of incompatible type %s",
					typename, shadow_typename);
			free(typename);
			free(shadow_typename);
		}
		obj->value = shadow_obj->value;
	}
	append_decl(ctx, &(struct declaration){
		.decl_type = DECL_CONST,
		.file = obj->idecl->decl.loc.file,
		.ident = obj->ident,
		.exported = obj->idecl->decl.exported,
		.constant = {
			.type = type,
			.value = obj->value,
		}
	});
}

static void
resolve_function(struct context *ctx, struct scope_object *obj)
{
	const struct ast_function_decl *decl = &obj->idecl->decl.function;

	const struct ast_type fn_atype = {
		.loc = obj->idecl->decl.loc,
		.storage = STORAGE_FUNCTION,
		.flags = 0,
		.func = decl->prototype,
	};
	const struct type *fntype = type_store_lookup_atype(ctx, &fn_atype);
	if (obj->idecl->decl.exported) {
		check_exported_type(ctx, obj->idecl->decl.loc, fntype);
	}

	obj->otype = O_DECL;
	obj->type = fntype;
}

static void
resolve_global(struct context *ctx, struct scope_object *obj)
{
	const struct ast_global_decl *decl = &obj->idecl->decl.global;
	const struct type *type = NULL;
	bool context = false;
	struct expression *init, *value = NULL;
	if (decl->type) {
		type = type_store_lookup_atype(ctx, decl->type);
		context = decl->type->storage == STORAGE_ARRAY
			&& decl->type->array.contextual;
		if (context && !decl->init) {
			error(ctx, decl->type->loc, NULL,
				"Cannot infer array length without an initializer");
			type = &builtin_type_error;
			goto end;
		}
	}

	if (decl->init) {
		init = xcalloc(1, sizeof(struct expression));
		value = xcalloc(1, sizeof(struct expression));
		check_expression(ctx, decl->init, init, type);
		if (type) {
			if (!type_is_assignable(ctx, type, init->result)) {
				char *typename1 = gen_typename(init->result);
				char *typename2 = gen_typename(type);
				error(ctx, decl->init->loc, value,
					"Initializer type %s is not assignable to global type %s",
					typename1, typename2);
				free(typename1);
				free(typename2);
				type = &builtin_type_error;
				goto end;
			}
		} else {
			type = lower_flexible(ctx, init->result, NULL);
		}
		if (context) {
			type = init->result;
		} else {
			init = lower_implicit_cast(ctx, type, init);
		}
		if (type->size == SIZE_UNDEFINED) {
			error(ctx, decl->init->loc, NULL,
				"Cannot initialize object with undefined size");
			type = &builtin_type_error;
			goto end;
		}
		assert(type->size != SIZE_UNDEFINED);
		if (type->storage == STORAGE_NULL) {
			error(ctx, decl->init->loc, NULL,
				"Can't initialize global as null without explicit type hint");
			type = &builtin_type_error;
			goto end;
		}
		if (!eval_expr(ctx, init, value)) {
			error(ctx, decl->init->loc, value,
				"Unable to evaluate initializer at compile time");
			type = &builtin_type_error;
			goto end;
		}
	}

	if (obj->idecl->decl.exported) {
		struct location loc =
			decl->type ? decl->type->loc : decl->init->loc;
		check_exported_type(ctx, loc, type);
	}

end:;
	struct ident *name = mkident(ctx, obj->name, NULL);
	obj->otype = O_DECL;
	obj->type = type;
	if (decl->threadlocal) {
		obj->flags |= SO_THREADLOCAL;
	}

	append_decl(ctx, &(struct declaration){
		.decl_type = DECL_GLOBAL,
		.file = obj->idecl->decl.loc.file,
		.ident = name,
		.symbol = ident_to_sym(ctx->itbl, obj->ident),

		.exported = obj->idecl->decl.exported,
		.global = {
			.type = type,
			.value = value,
			.threadlocal = obj->idecl->decl.global.threadlocal,
		}
	});
}

static void
resolve_enum_field(struct context *ctx, struct scope_object *obj)
{
	assert(obj->idecl->type == IDECL_ENUM_FLD);

	const struct type *type = obj->type;

	struct ident *localname = intern_name(ctx->itbl, obj->ident->name);
	struct scope_object *new =
		scope_lookup(obj->idecl->field->enum_scope, localname);
	if (new != obj) {
		wrap_resolver(ctx, new, resolve_enum_field);
		assert(new->otype == O_CONST);
		obj->otype = O_CONST;
		obj->value = new->value;
		return;
	}

	ctx->scope = obj->idecl->field->enum_scope;
	obj->value = xcalloc(1, sizeof(struct expression));
	obj->value->result = type;
	if (obj->idecl->field->field->value) { // explicit value
		struct expression *initializer =
			xcalloc(1, sizeof(struct expression));
		check_expression(ctx, obj->idecl->field->field->value,
				initializer, type->alias.type);

		if (!type_is_assignable(ctx, type->alias.type, initializer->result)) {
			char *inittypename = gen_typename(initializer->result);
			char *builtintypename = gen_typename(type->alias.type);
			error_norec(ctx, obj->idecl->field->field->value->loc,
				"Enum value type (%s) is not assignable from initializer type (%s) for value %s",
				builtintypename, inittypename, obj->ident->name);
		}

		initializer = lower_implicit_cast(ctx, type, initializer);
		if (!eval_expr(ctx, initializer, obj->value)) {
			error_norec(ctx, obj->idecl->field->field->value->loc,
				"Unable to evaluate constant initializer at compile time");
		}
	} else { // implicit value
		struct scope_object *next = obj->lnext;
		// find previous enum value
		wrap_resolver(ctx, next, resolve_enum_field);
		obj->value->type = EXPR_LITERAL;
		if (type_is_signed(ctx, type_dealias(ctx, type))) {
			if (next == NULL) {
				obj->value->literal.ival = 0;
			} else {
				obj->value->literal.ival = next->value->literal.ival + 1;
			}
		} else {
			if (next == NULL) {
				obj->value->literal.uval = 0;
			} else {
				obj->value->literal.uval = next->value->literal.uval + 1;
			}
		}
	}
	obj->otype = O_CONST;
}

static const struct type *
lookup_enum_type(struct context *ctx, const struct scope_object *obj)
{
	const struct type *enum_type = NULL;

	switch (obj->otype) {
	case O_SCAN: {
		if (obj->idecl->in_progress) {
			// Type alias cycle will be handled in check
			return NULL;
		}

		if (obj->idecl->type != IDECL_DECL ||
				obj->idecl->decl.decl_type != ADECL_TYPE) {
			return NULL;
		}

		if (obj->idecl->decl.type.type->storage == STORAGE_ENUM) {
			assert(false);
		} else if (obj->idecl->decl.type.type->storage == STORAGE_ALIAS) {
			ctx->scope->parent = obj->idecl->imports;
			const struct scope_object *new = scope_lookup(ctx->scope,
					obj->idecl->decl.type.type->alias);
			if (new) {
				obj->idecl->in_progress = true;
				enum_type = lookup_enum_type(ctx, new);
				obj->idecl->in_progress = false;
			}
		}
		break;
	}
	case O_TYPE:
		enum_type = obj->type;
		break;
	default:
		return NULL;
	}

	if (!enum_type) {
		return NULL;
	}

	enum_type = type_dealias(ctx, enum_type);
	if (enum_type->storage != STORAGE_ENUM) {
		return NULL;
	}
	return enum_type;
}

static void
scan_enum_field_aliases(struct context *ctx, struct scope_object *obj)
{
	const struct type *enum_type = lookup_enum_type(ctx, obj);

	if (!enum_type) {
		return;
	}

	// orig->type is (perhaps transitively) an alias of a resolved enum
	// type, which means its dependency graph is a linear chain of
	// resolved types ending with that enum, so we can immediately resolve it
	wrap_resolver(ctx, obj, resolve_type);

	for (const struct scope_object *val = enum_type->_enum.values->objects;
			val; val = val->lnext) {
		struct ast_enum_field *afield =
			xcalloc(1, sizeof(struct ast_enum_field));
		*afield = (struct ast_enum_field){
			.loc = (struct location){0}, // XXX: what to put here?
			.name = (struct ident *)val->name,
		};

		struct incomplete_enum_field *field =
			xcalloc(1, sizeof(struct incomplete_enum_field));
		*field = (struct incomplete_enum_field){
			.field = afield,
			.enum_scope = val->idecl->field->enum_scope,
		};

		struct ident *name =
			intern_ident(ctx->itbl, val->name->name, obj->name);
		struct scope_object *new = incomplete_decl_create(ctx,
				(struct location){0}, ctx->scope, name, name);
		new->idecl->type = IDECL_ENUM_FLD;
		new->type = obj->type;
		new->idecl->field = field;
	}
}

void
resolve_dimensions(struct context *ctx, struct scope_object *obj)
{
	if (obj->idecl->type != IDECL_DECL || obj->idecl->decl.decl_type != ADECL_TYPE) {
		struct location loc;
		if (obj->idecl->type == IDECL_ENUM_FLD) {
			loc = obj->idecl->field->field->loc;
		} else {
			loc = obj->idecl->decl.loc;
		}
		char *ident = ident_unparse(obj->name);
		error(ctx, loc, NULL, "'%s' is not a type", ident);
		free(ident);
		obj->type = &builtin_type_error;
		return;
	}
	struct dimensions dim = type_store_lookup_dimensions(ctx,
			obj->idecl->decl.type.type);
	obj->type = xcalloc(1, sizeof(struct type));
	*(struct type *)obj->type = (struct type){
		.size = dim.size,
		.align = dim.align,
	};
}

void
resolve_type(struct context *ctx, struct scope_object *obj)
{
	struct location loc;
	if (obj->idecl->type == IDECL_ENUM_FLD) {
		loc = obj->idecl->field->field->loc;
	} else {
		loc = obj->idecl->decl.loc;
	}

	if (obj->idecl->type != IDECL_DECL || obj->idecl->decl.decl_type != ADECL_TYPE) {
		error_norec(ctx, loc, "'%s' is not a type",
				ident_unparse(obj->name));
	}

	// compute type dimensions
	struct errors **cur_err = ctx->next;
	struct dimensions dim = type_store_lookup_dimensions(
			ctx, obj->idecl->decl.type.type);
	obj->idecl->in_progress = false;

	// compute type representation and store it
	struct type *alias = (struct type *)type_store_lookup_alias(ctx, obj->ident,
			obj->name, NULL, obj->idecl->decl.type.type->flags,
			obj->idecl->decl.exported);
	obj->otype = O_TYPE;
	obj->type = alias;
	if (ctx->next == cur_err) {
		alias->size = dim.size;
		alias->align = dim.align;
		alias->alias.type = type_store_lookup_atype(
			ctx, obj->idecl->decl.type.type);
	} else {
		alias->alias.type = &builtin_type_error;
	}
	assert(alias->alias.type != NULL);
	if (obj->idecl->decl.exported) {
		check_exported_type(ctx, obj->idecl->decl.type.type->loc,
			alias->alias.type);
	}
	if (alias->alias.type->storage == STORAGE_NEVER) {
		error(ctx, loc, NULL, "Can't declare type alias of never");
		alias->alias.type = &builtin_type_error;
	}

	append_decl(ctx, &(struct declaration){
		.decl_type = DECL_TYPE,
		.file = obj->idecl->decl.loc.file,
		.ident = obj->ident,
		.exported = obj->idecl->decl.exported,
		.type = alias,
	});
}

static struct scope_object *
scan_const(struct context *ctx, struct scope *imports, bool exported,
		struct location loc, const struct ast_global_decl *decl)
{
	struct ident *with_ns = mkident(ctx, decl->ident, NULL);
	check_hosted_main(ctx, loc, NULL, with_ns, NULL);
	struct scope_object *obj = incomplete_decl_create(ctx, loc,
				ctx->scope, with_ns, decl->ident);
	obj->idecl->type = IDECL_DECL;
	obj->idecl->decl = (struct ast_decl){
		.decl_type = ADECL_CONST,
		.loc = loc,
		.constant = *decl,
		.exported = exported,
	};
	obj->idecl->imports = imports;
	return obj;
}

static void
scan_decl(struct context *ctx, struct scope *imports, const struct ast_decl *decl)
{
	struct scope_object *obj;
	struct ident *ident;
	switch (decl->decl_type) {
	case ADECL_CONST:
		for (const struct ast_global_decl *g = &decl->constant;
				g; g = g->next) {
			scan_const(ctx, imports, decl->exported, decl->loc, g);
		}
		break;
	case ADECL_GLOBAL:
		for (const struct ast_global_decl *g = &decl->global;
				g; g = g->next) {
			ident = mkident(ctx, g->ident, g->symbol);
			check_hosted_main(ctx, decl->loc, NULL, ident, g->symbol);
			obj = incomplete_decl_create(ctx, decl->loc,
				ctx->scope, ident, g->ident);
			obj->idecl->type = IDECL_DECL;
			obj->idecl->decl = (struct ast_decl){
				.decl_type = ADECL_GLOBAL,
				.loc = decl->loc,
				.global = *g,
				.exported = decl->exported,
			};
			obj->idecl->imports = imports;
		}
		break;
	case ADECL_FUNC:;
		const struct ast_function_decl *func = &decl->function;
		struct ident *name;
		if (func->flags) {
			const char *template = NULL;
			if (func->flags & FN_TEST) {
				template = "testfunc.%d";
			} else if (func->flags & FN_INIT) {
				template = "initfunc.%d";
			} else if (func->flags & FN_FINI) {
				template = "finifunc.%d";
			}
			assert(template);
			ident = name = intern_generated(ctx, template);
		} else {
			ident = mkident(ctx, func->ident, func->symbol);
			name = func->ident;
		}
		obj = incomplete_decl_create(ctx, decl->loc,
			ctx->scope, ident, name);
		check_hosted_main(ctx, decl->loc, decl, ident, func->symbol);
		obj->idecl->type = IDECL_DECL;
		obj->idecl->decl = (struct ast_decl){
			.decl_type = ADECL_FUNC,
			.loc = decl->loc,
			.function = *func,
			.exported = decl->exported,
		};
		obj->idecl->imports = imports;
		break;
	case ADECL_TYPE:
		scan_types(ctx, imports, decl);
		break;
	case ADECL_ASSERT:;
		struct ident *id = intern_generated(ctx, "static_assert.%d");
		obj = incomplete_decl_create(ctx, decl->loc, ctx->scope, id, id);
		obj->idecl->type = IDECL_DECL;
		obj->idecl->decl = (struct ast_decl){
			.decl_type = ADECL_ASSERT,
			.loc = decl->loc,
			.assert = decl->assert,
			.exported = decl->exported,
		};
		obj->idecl->imports = imports;
		break;
	}
}

static void
resolve_decl(struct context *ctx, struct scope_object *obj)
{
	switch (obj->idecl->type) {
	case IDECL_ENUM_FLD:
		resolve_enum_field(ctx, obj);
		return;
	case IDECL_DECL:
		break;
	}

	switch (obj->idecl->decl.decl_type) {
	case ADECL_CONST:
		resolve_const(ctx, obj);
		return;
	case ADECL_GLOBAL:
		resolve_global(ctx, obj);
		return;
	case ADECL_FUNC:
		resolve_function(ctx, obj);
		return;
	case ADECL_TYPE:
		resolve_type(ctx, obj);
		return;
	case ADECL_ASSERT:;
		struct expression expr = {0};
		check_assert(ctx, obj->idecl->decl.assert, obj->idecl->decl.loc, &expr);
		return;
	}
	abort();
}

void
wrap_resolver(struct context *ctx, struct scope_object *obj, resolvefn resolver)
{
	// ensure this declaration wasn't already scanned
	if (!obj || obj->otype != O_SCAN) {
		return;
	}

	// save current subunit and enum context
	struct scope *scope = ctx->scope;
	struct scope *subunit = ctx->unit->parent;
	ctx->unit->parent = NULL;
	const struct type *fntype = ctx->fntype;
	ctx->fntype = NULL;
	struct ast_types *unresolved = ctx->unresolved;
	ctx->unresolved = NULL;

	// load this declaration's subunit context
	ctx->scope = ctx->defines;
	ctx->unit->parent = obj->idecl->imports;

	// resolving a declaration that is already in progress -> cycle
	if (obj->idecl->in_progress) {
		struct location loc;
		if (obj->idecl->type == IDECL_ENUM_FLD) {
			loc = obj->idecl->field->field->loc;
		} else {
			loc = obj->idecl->decl.loc;
		}
		error_norec(ctx, loc, "Circular dependency for '%s'",
			ident_unparse(obj->name));
	}
	obj->idecl->in_progress = true;

	resolver(ctx, obj);

	obj->idecl->in_progress = false;
	resolve_unresolved(ctx);
	// load stored context
	ctx->unresolved = unresolved;
	ctx->fntype = fntype;
	ctx->unit->parent = subunit;
	ctx->scope = scope;
}

static void
load_import(struct context *ctx, const struct ast_global_decl *defines,
	struct ast_imports *import, struct scope *scope)
{
	struct scope *mod = module_resolve(ctx, defines, import->ident);

	if (import->mode == IMPORT_MEMBERS) {
		for (const struct ast_import_members *member = import->members;
				member; member = member->next) {
			struct ident *ident = intern_ident(ctx->itbl,
					member->name->name, import->ident);
			const struct scope_object *obj = scope_lookup(mod, ident);
			if (!obj) {
				error_norec(ctx, member->loc, "Unknown object '%s'",
						ident_unparse(ident));
			}
			assert(obj->otype != O_SCAN);
			// obj->type and obj->value are a union, so it doesn't
			// matter which is passed into scope_insert
			struct scope_object *new = scope_insert(scope,
				obj->otype, obj->ident, member->name, obj->type, NULL);
			new->flags = obj->flags;
			if (obj->otype != O_TYPE
					|| type_dealias(ctx, obj->type)->storage
						!= STORAGE_ENUM) {
				continue;
			}
			const struct scope *enum_scope =
				type_dealias(ctx, obj->type)->_enum.values;
			for (const struct scope_object *o = enum_scope->objects;
					o; o = o->lnext) {
				struct ident *value_ident =
					intern_ident(ctx->itbl, o->name->name, ident);
				struct ident *value_name =
					intern_ident(ctx->itbl, o->name->name, member->name);
				scope_insert(scope, o->otype, value_ident,
					value_name, NULL, o->value);
			}
		}
		return;
	}

	struct ident *prefix = NULL;
	switch (import->mode) {
	case IMPORT_NORMAL:
		prefix = intern_name(ctx->itbl, import->ident->name);
		break;
	case IMPORT_ALIAS:
		prefix = intern_name(ctx->itbl, import->alias);
		break;
	case IMPORT_WILDCARD:
		prefix = NULL;
		break;
	case IMPORT_MEMBERS:
		abort(); // Unreachable
	}

	for (const struct scope_object *obj = mod->objects;
			obj; obj = obj->lnext) {
		assert(obj->otype != O_SCAN);

		struct scope_object *new;
		if (import->mode == IMPORT_NORMAL) {
			// obj->type and obj->value are a union, so it doesn't
			// matter which is passed into scope_insert
			new = scope_insert(scope, obj->otype, obj->ident,
				obj->name, obj->type, NULL);
			new->flags = obj->flags;
		}

		struct ident *name;
		if (obj->name->ns == NULL) {
			// this is only possible if an invalid .td file is used.
			// this check is necessary since the scope_lookup below
			// will segfault if obj->name.ns is NULL
			error_norec(ctx, (struct location){0},
				"Invalid typedefs for %s",
				ident_unparse(import->ident));
		}
		const struct scope_object *_enum = scope_lookup(mod, obj->name->ns);
		if (_enum != NULL && _enum->otype == O_TYPE
				&& type_dealias(NULL, _enum->type)->storage == STORAGE_ENUM) {
			// include enum type in ident if object is an enum
			// constant
			struct ident *ns =
				intern_ident(ctx->itbl, obj->name->ns->name, prefix);
			name = intern_ident(ctx->itbl, obj->name->name, ns);
		} else {
			name = intern_ident(ctx->itbl, obj->name->name, prefix);
		}
		// obj->type and obj->value are a union, so it doesn't matter
		// which is passed into scope_insert
		new = scope_insert(scope, obj->otype, obj->ident, name,
			obj->type, NULL);
		new->flags = obj->flags;
	}
}

static const struct location defineloc = {
	.file = 0,
	.lineno = 1,
	.colno = 1,
};

struct scope *
check_internal(type_store *ts,
	struct modcache **cache,
	bool is_test,
	const char *mainsym,
	struct ident *mainident,
	const struct ast_global_decl *defines,
	const struct ast_unit *aunit,
	struct unit *unit,
	struct intern_table *itbl,
	bool scan_only)
{
	struct context ctx = {0};
	ctx.ns = unit->ns;
	ctx.is_test = is_test;
	ctx.mainsym = mainsym;
	ctx.mainident = mainident;
	ctx.store = ts;
	ctx.next = &ctx.errors;
	ctx.modcache = cache;
	ctx.itbl = itbl;

	// Top-level scope management involves:
	//
	// - Creating a top-level scope for the whole unit, to which
	//   declarations are added.
	// - Creating a scope for each sub-unit, and populating it with imports.
	//
	// Further down the call frame, subsequent functions will create
	// sub-scopes for each declaration, expression-list, etc.

	// Put defines into a temporary scope (-D on the command line)
	sources[0] = "-D";
	ctx.scope = NULL;
	ctx.unit = scope_push(&ctx.scope, SCOPE_DEFINES);
	for (const struct ast_global_decl *def = defines; def; def = def->next) {
		struct scope_object *obj =
			scan_const(&ctx, NULL, false , defineloc, def);
		resolve_const(&ctx, obj);
	}
	ctx.defines = ctx.scope;
	ctx.scope = NULL;
	ctx.defines->parent = ctx.unit = scope_push(&ctx.scope, SCOPE_UNIT);
	sources[0] = "<unknown>";

	// Populate the imports and put declarations into a scope.
	// Each declaration holds a reference to its subunit's imports
	// A scope gets us:
	//  a) duplicate detection for free
	//  b) a way to find declaration's definition when it's refered to
	struct scopes *subunit_scopes = NULL, **next = &subunit_scopes;
	struct scope *su_scope = NULL;
	struct identifiers **inext = &unit->imports;
	for (const struct ast_subunit *su = &aunit->subunits;
			su; su = su->next) {
		su_scope = NULL;
		scope_push(&su_scope, SCOPE_SUBUNIT);
		for (struct ast_imports *imports = su->imports;
				imports; imports = imports->next) {
			load_import(&ctx, defines, imports, su_scope);

			bool found = false;
			for (struct identifiers *uimports = unit->imports;
					uimports; uimports = uimports->next) {
				if (uimports->ident == imports->ident) {
					found = true;
					break;
				}
			}
			if (!found) {
				struct identifiers *uimport = *inext =
					xcalloc(1, sizeof(struct identifiers));
				uimport->ident = imports->ident;
				inext = &uimport->next;
			}
		}

		for (struct ast_decls *d = su->decls; d; d = d->next) {
			scan_decl(&ctx, su_scope, &d->decl);
		}

		*next = xcalloc(1, sizeof(struct scopes));
		(*next)->scope = su_scope;
		next = &(*next)->next;
	}

	// Find enum aliases and store them in incomplete enum value declarations
	for (struct scope_object *obj = ctx.scope->objects;
			obj; obj = obj->lnext) {
		scan_enum_field_aliases(&ctx, obj);
	}

	// XXX: shadowed declarations are not checked for consistency
	ctx.scope = ctx.defines;

	for (const struct scope_object *obj = ctx.scope->objects;
			obj; obj = obj->lnext) {
		const struct scope_object *shadowed_obj =
			scope_lookup(ctx.unit, obj->name);
		if (!shadowed_obj) {
			continue;
		}
		if (shadowed_obj->otype == O_CONST) {
			continue;
		}
		if (shadowed_obj->otype == O_SCAN) {
			if (shadowed_obj->idecl->type == IDECL_DECL &&
					shadowed_obj->idecl->decl.decl_type == ADECL_CONST) {
				continue;
			}
		}
		error(&ctx, defineloc, NULL, "Define shadows a non-define object");
	}

	// Perform actual declaration resolution
	for (struct scope_object *obj = ctx.unit->objects;
			obj; obj = obj->lnext) {
		wrap_resolver(&ctx, obj, resolve_decl);
		// populate the expression graph
		if (obj->idecl->type == IDECL_DECL && obj->idecl->decl.decl_type == ADECL_FUNC) {
			ctx.unit->parent = obj->idecl->imports;
			check_function(&ctx, obj, &obj->idecl->decl);
		}
	}

	assert(ctx.unresolved == NULL);
	handle_errors(ctx.errors);
	unit->declarations = ctx.decls;

	if (!(scan_only || unit->declarations)) {
		xfprintf(stderr, "Error: module contains no declarations\n");
		exit(EXIT_CHECK);
	}

	ctx.unit->parent = NULL;
	return ctx.unit;
}

struct scope *
check(type_store *ts,
	bool is_test,
	const char *mainsym,
	struct ident *mainident,
	const struct ast_global_decl *defines,
	const struct ast_unit *aunit,
	struct unit *unit,
	struct intern_table *itbl)
{
	struct modcache *modcache[MODCACHE_BUCKETS] = {0};
	return check_internal(ts, modcache, is_test, mainsym, mainident, defines, aunit, unit, itbl, false);
}

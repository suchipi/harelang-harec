#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "check.h"
#include "eval.h"
#include "identifier.h"
#include "scope.h"
#include "type_store.h"
#include "types.h"
#include "util.h"

static struct dimensions
dim_from_type(const struct type *type)
{
	return (struct dimensions){ .size = type->size, .align = type->align };
}

static size_t
ast_array_len(struct context *ctx, const struct ast_type *atype)
{
	// TODO: Maybe we should cache these
	struct expression in, out;
	if (atype->array.length == NULL) {
		return SIZE_UNDEFINED;
	}
	check_expression(ctx, atype->array.length, &in, NULL);
	if (!eval_expr(ctx, &in, &out)) {
		error(ctx, atype->loc, NULL,
			"Cannot evaluate array length at compile time");
		return SIZE_UNDEFINED;
	}
	if (!type_is_integer(ctx, out.result)) {
		error(ctx, atype->loc, NULL, "Array length must be an integer");
		return SIZE_UNDEFINED;
	}
	if (type_is_signed(ctx, out.result) && out.literal.ival < 0) {
		error(ctx, atype->loc, NULL,
			"Array length must be non-negative");
		return SIZE_UNDEFINED;
	}
	return (size_t)out.literal.uval;
}

const struct type *
builtin_type_for_storage(enum type_storage storage)
{
	switch (storage) {
	case STORAGE_BOOL:
		return &builtin_type_bool;
	case STORAGE_INVALID:
		return &builtin_type_invalid;
	case STORAGE_F32:
		return &builtin_type_f32;
	case STORAGE_F64:
		return &builtin_type_f64;
	case STORAGE_I8:
		return &builtin_type_i8;
	case STORAGE_I16:
		return &builtin_type_i16;
	case STORAGE_I32:
		return &builtin_type_i32;
	case STORAGE_I64:
		return &builtin_type_i64;
	case STORAGE_INT:
		return &builtin_type_int;
	case STORAGE_NEVER:
		return &builtin_type_never;
	case STORAGE_NOMEM:
		return &builtin_type_nomem;
	case STORAGE_OPAQUE:
		return &builtin_type_opaque;
	case STORAGE_RUNE:
		return &builtin_type_rune;
	case STORAGE_SIZE:
		return &builtin_type_size;
	case STORAGE_U8:
		return &builtin_type_u8;
	case STORAGE_U16:
		return &builtin_type_u16;
	case STORAGE_U32:
		return &builtin_type_u32;
	case STORAGE_U64:
		return &builtin_type_u64;
	case STORAGE_UINT:
		return &builtin_type_uint;
	case STORAGE_UINTPTR:
		return &builtin_type_uintptr;
	case STORAGE_VALIST:
		return &builtin_type_valist;
	case STORAGE_VOID:
		return &builtin_type_void;
	case STORAGE_DONE:
		return &builtin_type_done;
	case STORAGE_NULL:
		return &builtin_type_null;
	case STORAGE_STRING:
		return &builtin_type_str;
	case STORAGE_UNDEFINED:
		return &builtin_type_undefined;
	case STORAGE_ALIAS:
	case STORAGE_ARRAY:
	case STORAGE_ERROR:
	case STORAGE_FUNCTION:
	case STORAGE_FCONST:
	case STORAGE_ICONST:
	case STORAGE_RCONST:
	case STORAGE_POINTER:
	case STORAGE_SLICE:
	case STORAGE_STRUCT:
	case STORAGE_TAGGED:
	case STORAGE_TUPLE:
	case STORAGE_UNION:
	case STORAGE_ENUM:
		return NULL;
	}
	assert(0); // Unreachable
}

static const struct type *
builtin_for_type(const struct type *type)
{
	return builtin_type_for_storage(type->storage);
}

static bool
struct_union_has_field(struct context *ctx,
	const char *name,
	const struct struct_field *fields)
{
	for (; fields; fields = fields->next) {
		if (fields->name != NULL) {
			if (strcmp(fields->name, name) == 0) {
				return true;
			}
			continue;
		}

		assert(fields->type != NULL);
		const struct type *type = type_dealias(ctx, fields->type);
		if (struct_union_has_field(ctx, name, type->struct_union.fields)) {
			return true;
		}
	}

	return false;
}

static struct struct_field *
struct_new_field(struct context *ctx, struct type *type,
	const struct ast_struct_union_field *afield,
	size_t *offset, bool size_only)
{
	bool named = afield->name != NULL && strcmp(afield->name, "_") != 0;
	if (named && !size_only) {
		if (struct_union_has_field(ctx, afield->name, type->struct_union.fields)) {
			error(ctx, afield->type->loc, NULL,
				"Duplicate struct/union member '%s'",
				afield->name);
			return NULL;
		}
	}
	struct struct_field *field = xcalloc(1, sizeof(struct struct_field));

	if (afield->name && !size_only) {
		field->name = afield->name;
	}
	struct dimensions dim = {0};
	if (size_only) {
		dim = type_store_lookup_dimensions(ctx, afield->type);
	} else {
		field->type = type_store_lookup_atype(ctx, afield->type);
		dim = dim_from_type(field->type);
	}
	if (afield->next != NULL && dim.size == SIZE_UNDEFINED) {
		error(ctx, afield->type->loc, NULL,
			"Type of undefined size is not a valid struct/union member");
		return NULL;
	}
	if (dim.align == ALIGN_UNDEFINED) {
		error(ctx, afield->type->loc, NULL,
			"Type of undefined alignment is not a valid struct/union member");
		return NULL;
	}

	type->align = dim.align > type->align ? dim.align : type->align;
	field->size = dim.size;

	if (type->storage == STORAGE_UNION) {
		field->offset = 0;
		if (dim.size == SIZE_UNDEFINED || type->size == SIZE_UNDEFINED) {
			type->size = SIZE_UNDEFINED;
		} else {
			type->size = dim.size > type->size ? dim.size : type->size;
		}
		return field;
	}

	if (type->struct_union.packed) {
		field->offset = *offset = type->size;
	} else {
		*offset = type->size;
		if (dim.align != 0 && *offset % dim.align) {
			*offset += dim.align - (*offset % dim.align);
		}
		field->offset = *offset;
		assert(dim.align == 0 || field->offset % dim.align == 0);
	}

	if (dim.size == SIZE_UNDEFINED || type->size == SIZE_UNDEFINED) {
		type->size = SIZE_UNDEFINED;
	} else {
		type->size = field->offset + dim.size;
	}
	return field;
}

static const struct type *type_store_lookup_type(struct context *ctx,
		const struct type *type);

static bool
check_embedded_member(struct context *ctx,
	const struct ast_struct_union_field *afield,
	struct struct_field *member,
	const struct struct_field *fields)
{
	assert(member->type != NULL);
	const struct type *dealiased = type_dealias(ctx, member->type);
	if (dealiased->storage != STORAGE_STRUCT
			&& dealiased->storage != STORAGE_UNION) {
		error(ctx, afield->type->loc, NULL,
			"Cannot embed non-struct non-union alias");
		member->type = &builtin_type_invalid;
		return false;
	}

	for (struct struct_field *field = dealiased->struct_union.fields;
			field; field = field->next) {
		if (field->name != NULL) {
			if (strcmp(field->name, "_") == 0) {
				continue;
			}
			if (struct_union_has_field(ctx, field->name, fields)) {
				// XXX: the location could be better
				error(ctx, afield->type->loc, NULL,
					"Duplicate struct/union member '%s'",
					field->name);
				return false;
			}
		} else {
			if (!check_embedded_member(ctx, afield, field, fields)) {
				return false;
			}
		}
	}

	return true;
}

static void
shift_fields(struct context *ctx,
	const struct ast_struct_union_field *afield, struct struct_field *parent)
{
	if (parent->offset == 0) {
		// We need to return early here in order to avoid dealiasing an
		// embedded alias. This is acceptable at nonzero offsets, but we
		// need to keep the alias if it's at offset 0 because of
		// subtyping.
		return;
	}
	const struct type *type = type_dealias(ctx, parent->type);
	assert(type->storage == STORAGE_STRUCT
		|| type->storage == STORAGE_UNION);
	struct type new = {
		.storage = type->storage,
		.size = type->size,
		.align = type->align,
		.struct_union.packed = type->struct_union.packed,
	};
	struct struct_field **next = &new.struct_union.fields;
	for (struct struct_field *field = type->struct_union.fields; field;
			field = field->next) {
		struct struct_field *new = *next =
			xcalloc(1, sizeof(struct struct_field));
		next = &new->next;
		new->type = field->type;
		new->offset = parent->offset;
		if (field->name) {
			new->name = field->name;
		} else {
			shift_fields(ctx, NULL, new);
		}
		// Sub-subfields are shifted by field->offset in the recursive
		// shift_fields call, delay adding it to new->offset to avoid
		// shifting by field->offset twice
		new->offset += field->offset;
	}

	parent->type = type_store_lookup_type(ctx, &new);
}

static bool
struct_init_from_atype(struct context *ctx, struct type *type,
	const struct ast_type *atype, bool size_only)
{
	// TODO: fields with size SIZE_UNDEFINED
	type->struct_union.packed = atype->struct_union.packed;

	size_t offset = 0;
	assert(type->storage == STORAGE_STRUCT || type->storage == STORAGE_UNION);
	struct struct_field **next = &type->struct_union.fields;
	for (const struct ast_struct_union_field *afield = &atype->struct_union.fields;
			afield; afield = afield->next) {
		struct struct_field *field = struct_new_field(ctx, type,
			afield, &offset, size_only);
		if (field == NULL) {
			return false;
		}
		if (size_only) {
			free(field);
			continue;
		} else if (!field->name) {
			if (!check_embedded_member(ctx, afield, field,
						type->struct_union.fields)) {
				return false;
			}
			// We need to shift the embedded struct/union's fields
			// so that their offsets are from the start of the
			// parent type. This is a bit of a hack, but it makes
			// type_get_field far easier to implement and doesn't
			// cause any trouble in gen since offsets are only used
			// there for sorting fields.
			shift_fields(ctx, afield, field);
		}
		*next = field;
		next = &field->next;
	}
	return true;
}

static void
add_padding(size_t *size, size_t align)
{
	if (*size != SIZE_UNDEFINED && *size != 0 && *size % align != 0) {
		*size += align - *size % align;
	}
}

static void
size_with_tag(struct dimensions *out, struct dimensions new)
{
	if (new.size == SIZE_UNDEFINED || out->size == SIZE_UNDEFINED) {
		out->size = SIZE_UNDEFINED;
		out->align = ALIGN_UNDEFINED;
		return;
	}
	assert(new.align != ALIGN_UNDEFINED && out->align != ALIGN_UNDEFINED);

	size_t sz = new.size + builtin_type_u32.size;
	size_t align = new.align;
	if (align < builtin_type_u32.align) {
		align = builtin_type_u32.align;
	}
	add_padding(&sz, align);

	if (sz > out->size) {
		out->size = sz;
	}
	if (align > out->align) {
		out->align = align;
	}
}

static struct dimensions
tagged_size(struct context *ctx, const struct ast_tagged_union_type *atype)
{
	struct dimensions ret = { 0 };
	assert(atype != NULL);
	for (; atype; atype = atype->next) {
		if (!atype->unwrap) {
			size_with_tag(&ret,
				type_store_lookup_dimensions(ctx, atype->type));
			continue;
		}

		const struct type *unwrapped =
			type_store_lookup_atype(ctx, atype->type);
		unwrapped = type_dealias(ctx, unwrapped);
		if (unwrapped->storage != STORAGE_TAGGED) {
			if (unwrapped->storage != STORAGE_INVALID) {
				error(ctx, atype->type->loc, NULL,
					"Can't reduce non-tagged-union type %s",
					gen_typename(unwrapped));
			}
			return ret;
		}

		for (size_t i = 0; i < unwrapped->tagged.len; i++) {
 			const struct type *mtype = unwrapped->tagged.types[i];
			size_with_tag(&ret, dim_from_type(mtype));
		}
	}
	return ret;
}

static int
tagged_cmp(const void *_a, const void *_b)
{
	const struct type *a = *(const struct type **)_a;
	const struct type *b = *(const struct type **)_b;
	return a->id < b->id ? -1 : a->id > b->id ? 1 : 0;
}

static void
tagged_init(struct context *ctx, struct type *type,
	struct location loc, bool valid)
{
	const struct type **membs = type->tagged.types;

	// Lower flexible constants
	// TODO: Don't do this if !valid, and handle flexible literals properly
	// in result type reduction
	for (size_t i = 0; i < type->tagged.len; i++) {
		membs[i] = lower_flexible(ctx, membs[i], NULL);
	}

	// Then sort by ID
	qsort(membs, type->tagged.len, sizeof(membs[0]), tagged_cmp);

	// Then deduplicate and enforce validity
	size_t dedup_len = 1;
	bool invalid = false;
	for (size_t i = 1; i < type->tagged.len; i++) {
		if (membs[i]->id != membs[i - 1]->id) {
			membs[dedup_len++] = membs[i];
		} else if (!type_equal(membs[i], membs[i - 1])) {
			char *first_name = gen_typename(membs[i - 1]);
			char *second_name = gen_typename(membs[i]);
			error(ctx, loc, NULL, "Hash collision between %s and %s",
				first_name, second_name);
		}
		if (membs[i]->storage == STORAGE_NULL && valid) {
			error(ctx, loc, NULL,
				"Null type not allowed in this context");
			invalid = true;
		}
		if (membs[i]->size == SIZE_UNDEFINED && valid) {
			error(ctx, loc, NULL,
				"Type of undefined size is not a valid tagged union member");
			invalid = true;
		}
		assert(membs[i]->align != ALIGN_UNDEFINED || invalid || !valid);
	}
	if (dedup_len < type->tagged.len) {
		type->tagged.len = dedup_len;
	}

	if (invalid) {
		*type = builtin_type_invalid;
		return;
	}

	struct dimensions dims = {0};
	size_with_tag(&dims, dim_from_type(&builtin_type_void));
	for (size_t i = 0; i < type->tagged.len; i++) {
		size_with_tag(&dims, dim_from_type(membs[i]));
	}
	type->size = dims.size;
	type->align = dims.align;
}

static void
tagged_init_from_atype(struct context *ctx,
	struct type *type, const struct ast_type *atype)
{
	assert(atype->storage == STORAGE_TAGGED);
	const struct ast_tagged_union_type *amemb = &atype->tagged;
	type->tagged.types = NULL;
	type->tagged.len = 0;
	type->tagged.cap = 0;
	for (; amemb; amemb = amemb->next) {
		const struct type *memb =
			type_store_lookup_atype(ctx, amemb->type);
		if (!amemb->unwrap) {
			tagged_append(&type->tagged, memb);
			continue;
		}

		memb = type_dealias(ctx, memb);
		if (memb->storage != STORAGE_TAGGED) {
			if (memb->storage != STORAGE_INVALID) {
				error(ctx, atype->loc, NULL,
					"Can't reduce non-tagged-union type %s",
					gen_typename(memb));
			}
			*type = builtin_type_invalid;
			return;
		}
		assert(memb->storage == STORAGE_TAGGED);
		for (size_t i = 0; i < memb->tagged.len; i++) {
			tagged_append(&type->tagged, memb->tagged.types[i]);
		}
	}
	tagged_init(ctx, type, atype->loc, true);

	if (type->tagged.len <= 1) {
		error(ctx, atype->loc, NULL,
			"Tagged unions must have at least two distinct members");
		*type = builtin_type_invalid;
	}
}

static struct dimensions
tuple_init_from_atype(struct context *ctx,
	struct type *type, const struct ast_type *atype)
{
	const struct ast_tuple_type *atuple = &atype->tuple;
	struct type_tuple *cur = NULL;
	if (type) {
		type->size = 0, type->align = 0;
		cur = &type->tuple;
	}
	struct dimensions dim = {0};
	while (atuple) {
		struct dimensions memb = {0};
		if (type) {
			cur->type = type_store_lookup_atype(ctx, atuple->type);
			memb = dim_from_type(cur->type);
		} else {
			memb = type_store_lookup_dimensions(ctx, atuple->type);
		}
		if (memb.size == SIZE_UNDEFINED) {
			error(ctx, atype->loc, NULL,
				"Type of undefined size is not a valid tuple member");
			if (type) {
				*type = builtin_type_invalid;
			}
			return (struct dimensions){0};
		}
		size_t offset = dim.size;
		if (memb.align != 0) {
			if (dim.size % memb.align) {
				offset += memb.align - dim.size % memb.align;
			}
			// offset = (dim.size + memb.align - 1) & (~(memb.align - 1));
			dim.size = offset + memb.size;
		}
		if (dim.align < memb.align) {
			dim.align = memb.align;
		}

		atuple = atuple->next;
		if (type) {
			cur->offset = offset;
			if (atuple) {
				cur->next = xcalloc(1, sizeof(struct type_tuple));
				cur = cur->next;
			}
		}
	}
	if (type) {
		type->size = dim.size;
		type->align = dim.align;
	}
	return dim;
}

static bool
default_param_from_atype(struct context *ctx,
	const struct ast_function_parameters *aparam,
	struct type_func_param *param)
{
	// This is leaked. check_expression makes a flexible ref that may be
	// updated later, so it cannot be on the stack.
	struct expression *in = xcalloc(1, sizeof(struct expression));
	check_expression(ctx, aparam->default_value, in, param->type);
	if (in->result->storage == STORAGE_INVALID) {
		return false;
	}
	if (!type_is_assignable(ctx, param->type, in->result)) {
		char *restypename = gen_typename(in->result);
		char *partypename = gen_typename(param->type);
		error(ctx, aparam->loc, NULL,
			"Result value %s is not assignable to parameter type %s",
			restypename, partypename);
		free(restypename);
		free(partypename);
		return false;
	}
	param->default_value = xcalloc(1, sizeof(struct expression));
	struct expression *cast = lower_implicit_cast(ctx, param->type, in);
	if (!eval_expr(ctx, cast, param->default_value)) {
		error(ctx, aparam->loc, NULL,
			"Unable to evaluate default parameter at compile time");
		return false;
	}
	// TODO remove this check once it works
	if (param->default_value->result->storage == STORAGE_POINTER &&
			param->default_value->literal.object != NULL) {
		error(ctx, aparam->loc, NULL,
			"Non-null pointer optional parameters are not currently supported. Will fix.");
		return false;
	}
	return true;
}

static struct dimensions
type_init_from_atype(struct context *ctx,
	struct type *type,
	const struct ast_type *atype)
{
	struct type tmp = {0};
	bool size_only = false;
	if (type == NULL) {
		type = &tmp;
		size_only = true;
	}

	type->storage = atype->storage;

	struct scope_object *obj = NULL;
	const struct type *builtin;
	switch (type->storage) {
	case STORAGE_INVALID:
	case STORAGE_FCONST:
	case STORAGE_ICONST:
	case STORAGE_RCONST:
	case STORAGE_ENUM:
	case STORAGE_NULL:
		assert(0); // Invariant
	case STORAGE_DONE:
	case STORAGE_NEVER:
	case STORAGE_BOOL:
	case STORAGE_F32:
	case STORAGE_F64:
	case STORAGE_I8:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_INT:
	case STORAGE_NOMEM:
	case STORAGE_OPAQUE:
	case STORAGE_RUNE:
	case STORAGE_SIZE:
	case STORAGE_STRING:
	case STORAGE_U8:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_UINT:
	case STORAGE_UINTPTR:
	case STORAGE_UNDEFINED:
	case STORAGE_VALIST:
	case STORAGE_VOID:
		builtin = builtin_type_for_storage(type->storage);
		type->size = builtin->size;
		type->align = builtin->align;
		break;
	case STORAGE_ERROR:;
		struct dimensions dims = { 0 };
		if (!size_only) {
			type->error = type_store_lookup_atype(ctx, atype->error);
			enum type_storage secondary = type_dealias(ctx, type->error)->storage;
			if (secondary == STORAGE_DONE || secondary == STORAGE_NEVER) {
				error(ctx, atype->loc, NULL,
					"%s cannot be an error",
					type_storage_unparse(secondary));
				*type = builtin_type_invalid;
				return (struct dimensions){0};
			}
			dims = dim_from_type(type->error);
		} else {
			dims = type_store_lookup_dimensions(ctx, atype->error);
		}
		type->size = dims.size;
		type->align = dims.align;
		break;
	case STORAGE_ALIAS:
		obj = scope_lookup(ctx->scope, atype->alias);
		if (!obj) {
			char *ident = ident_unparse(atype->alias);
			error(ctx, atype->loc, NULL,
				"Unresolvable identifier '%s'", ident);
			free(ident);
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}

		if (obj->otype == O_SCAN) {
			// an incomplete declaration was encountered
			if (size_only && obj->idecl->type == IDECL_DECL) {
				wrap_resolver(ctx, obj, resolve_dimensions);
				type->size = obj->type->size;
				type->align = obj->type->align;
				break;
			}
			// complete it first and then proceed normally
			wrap_resolver(ctx, obj, resolve_type);
		}

		if (obj->otype != O_TYPE) {
			char *ident = ident_unparse(obj->ident);
			error(ctx, atype->loc, NULL,
				"Object '%s' is not a type", ident);
			free(ident);
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}

		type->storage = obj->type->storage;
		if (obj->type->storage == STORAGE_ENUM) {
			type->_enum = obj->type->_enum;
		}
		type->alias.ident = obj->ident;
		type->alias.name = obj->name;
		type->alias.type = obj->type->alias.type;
		type->alias.exported = obj->type->alias.exported;
		type->size = obj->type->size;
		type->align = obj->type->align;
		break;
	case STORAGE_ARRAY:
		type->array.length = ast_array_len(ctx, atype);
		struct dimensions memb = {0};
		if (size_only) {
			memb = type_store_lookup_dimensions(ctx,
				atype->array.members);
		} else {
			type->array.members = type_store_lookup_atype(ctx,
				atype->array.members);
			memb = dim_from_type(type->array.members);
			if (type->array.members->storage == STORAGE_INVALID) {
				*type = builtin_type_invalid;
				return (struct dimensions){0};
			}
		}
		if (memb.size == 0) {
			error(ctx, atype->loc, NULL,
				"Type of size 0 is not a valid array member");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (memb.size == SIZE_UNDEFINED) {
			error(ctx, atype->loc, NULL,
				"Type of undefined size is not a valid array member");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}

		type->align = memb.align;
		if (type->array.length == SIZE_UNDEFINED) {
			type->size = SIZE_UNDEFINED;
		} else {
			type->size = memb.size * type->array.length;
		}
		break;
	case STORAGE_FUNCTION:
		type->size = SIZE_UNDEFINED;
		type->align = ALIGN_UNDEFINED;
		if (size_only) {
			break;
		}
		type->func.result = type_store_lookup_atype(ctx,
				atype->func.result);
		type->func.variadism = atype->func.variadism;
		struct type_func_param *param, **next = &type->func.params;
		bool has_optional = false;
		for (struct ast_function_parameters *aparam = atype->func.params;
				aparam; aparam = aparam->next) {
			param = *next = xcalloc(1, sizeof(struct type_func_param));
			param->type = type_store_lookup_atype(ctx, aparam->type);
			if (param->type->size == SIZE_UNDEFINED) {
				error(ctx, atype->loc, NULL,
					"Function parameter types must have defined size");
				*type = builtin_type_invalid;
				return (struct dimensions){0};
			}
			if (aparam->default_value != NULL) {
				has_optional = true;
				if (!default_param_from_atype(ctx,
						aparam, param)) {
					*type = builtin_type_invalid;
					return (struct dimensions){0};
				}
			} else if (atype->func.variadism == VARIADISM_HARE
					&& !aparam->next) {
				param->type = type_store_lookup_slice(
					ctx, aparam->loc, param->type);
			} else if (has_optional) {
				error(ctx, atype->loc, NULL,
					"Required function parameter may not follow optional parameters");
				*type = builtin_type_invalid;
				return (struct dimensions){0};
			}
			next = &param->next;
		}
		break;
	case STORAGE_POINTER:
		type->size = builtin_type_uintptr.size;
		type->align = builtin_type_uintptr.align;
		if (size_only) {
			break;
		}
		type->pointer.nullable = atype->pointer.nullable;
		type->pointer.referent = type_store_lookup_atype(
			ctx, atype->pointer.referent);
		if (type->pointer.referent->storage == STORAGE_INVALID) {
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (type->pointer.referent->size == 0) {
			error(ctx, atype->loc, NULL,
				"Can't have pointer to zero-sized type");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (type->pointer.referent->storage == STORAGE_NEVER) {
			error(ctx, atype->loc, NULL,
				"Can't have pointer to never");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		break;
	case STORAGE_SLICE:
		type->size = builtin_type_uintptr.size
			+ 2 * builtin_type_size.size;
		type->align = builtin_type_uintptr.align;
		if (size_only) {
			break;
		}
		type->array.members = type_store_lookup_atype(ctx,
				atype->slice.members);
		if (type->array.members->storage == STORAGE_INVALID) {
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (type->array.members->size == 0) {
			error(ctx, atype->loc, NULL,
				"Type of size 0 is not a valid slice member");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (type->array.members->storage == STORAGE_NEVER) {
			error(ctx, atype->loc, NULL,
				"never is not a valid slice member");
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		type->array.length = SIZE_UNDEFINED;
		break;
	case STORAGE_STRUCT:
	case STORAGE_UNION:
		if (!struct_init_from_atype(ctx, type, atype, size_only)) {
			*type = builtin_type_invalid;
			return (struct dimensions){0};
		}
		if (type->storage == STORAGE_UNION || !type->struct_union.packed) {
			add_padding(&type->size, type->align);
		}
		break;
	case STORAGE_TAGGED:
		if (size_only) {
			struct dimensions dims =
				tagged_size(ctx, &atype->tagged);
			type->size = dims.size;
			type->align = dims.align;
		} else {
			tagged_init_from_atype(ctx, type, atype);
		}
		add_padding(&type->size, type->align);
		break;
	case STORAGE_TUPLE:
		if (size_only) {
			struct dimensions tup;
			tup = tuple_init_from_atype(ctx, NULL, atype);
			type->size = tup.size;
			type->align = tup.align;
		} else {
			tuple_init_from_atype(ctx, type, atype);
		}
		add_padding(&type->size, type->align);
		break;
	}
	return dim_from_type(type);
}

static const struct type *
type_store_lookup_type(struct context *ctx, const struct type *type)
{
	const struct type *builtin = builtin_for_type(type);
	if (builtin) {
		return builtin;
	}

	uint32_t hash = type_hash(type);
	struct type_bucket **next = &(*ctx->store)[hash % TYPE_STORE_BUCKETS],
		*bucket = NULL;

	while (*next) {
		bucket = *next;
		if (bucket->type.id == hash) {
			if (!type_equal(&bucket->type, type)) {
				next = &bucket->next;
				continue;
			}
			if (bucket->type.storage == STORAGE_ALIAS) {
				type = type->alias.type;
				bucket->type.alias.type = type;
				if (type && type->storage == STORAGE_INVALID) {
					return &builtin_type_invalid;
			}
			}
			return &bucket->type;
		}
		next = &bucket->next;
	}

	bucket = *next = xcalloc(1, sizeof(struct type_bucket));
	bucket->type = *type;
	bucket->type.id = hash;
	return &bucket->type;
}

const struct type *
type_store_lookup_atype(struct context *ctx, const struct ast_type *atype)
{
	if (atype->storage == STORAGE_NULL) {
		return &builtin_type_null;
	}
	struct type temp = {0};
	type_init_from_atype(ctx, &temp, atype);
	return type_store_lookup_type(ctx, &temp);
}

// Compute dimensions of an incomplete type without completing it
struct dimensions
type_store_lookup_dimensions(struct context *ctx, const struct ast_type *atype)
{
	return type_init_from_atype(ctx, NULL, atype);
}

const struct type *
type_store_lookup_pointer(struct context *ctx, struct location loc,
	const struct type *referent, bool nullable)
{
	if (referent->storage == STORAGE_INVALID) {
		return &builtin_type_invalid;
	}
	if (referent->storage == STORAGE_NULL) {
		error(ctx, loc, NULL, "Null type not allowed in this context");
		return &builtin_type_invalid;
	}
	if (referent->size == 0) {
		error(ctx, loc, NULL, "Can't have pointer to zero-sized type");
		return &builtin_type_invalid;
	}
	if (referent->storage == STORAGE_NEVER) {
		error(ctx, loc, NULL, "Can't have pointer to never");
		return &builtin_type_invalid;
	}
	referent = lower_flexible(ctx, referent, NULL);

	struct type ptr = {
		.storage = STORAGE_POINTER,
		.pointer = {
			.referent = referent,
			.nullable = nullable,
		},
		.size = builtin_type_uintptr.size,
		.align = builtin_type_uintptr.align,
	};
	return type_store_lookup_type(ctx, &ptr);
}

const struct type *
type_store_lookup_array(struct context *ctx, struct location loc,
	const struct type *members, size_t len, bool expandable)
{
	if (members->storage == STORAGE_INVALID) {
		return &builtin_type_invalid;
	}
	if (members->storage == STORAGE_NULL) {
		error(ctx, loc, NULL, "Null type not allowed in this context");
		return &builtin_type_invalid;
	}
	members = lower_flexible(ctx, members, NULL);
	if (members->size == 0) {
		error(ctx, loc, NULL,
			"Type of size 0 is not a valid array member");
		return &builtin_type_invalid;
	}
	if (members->size == SIZE_UNDEFINED) {
		error(ctx, loc, NULL,
			"Type of undefined size is not a valid member of a bounded array");
		return &builtin_type_invalid;
	}
	assert(members->align != 0);
	assert(members->align != ALIGN_UNDEFINED);

	struct type array = {
		.storage = STORAGE_ARRAY,
		.array = {
			.members = members,
			.length = len,
			// TODO: Define expandable semantics better in spec
			.expandable = expandable,
		},
		.size = len == SIZE_UNDEFINED
			? SIZE_UNDEFINED : members->size * len,
		.align = members->align,
	};
	return type_store_lookup_type(ctx, &array);
}

const struct type *
type_store_lookup_slice(struct context *ctx, struct location loc,
	const struct type *members)
{
	if (members->storage == STORAGE_INVALID) {
		return &builtin_type_invalid;
	}
	if (members->storage == STORAGE_NULL) {
		error(ctx, loc, NULL, "Null type not allowed in this context");
		return &builtin_type_invalid;
	}
	members = lower_flexible(ctx, members, NULL);
	if (members->size == 0) {
		error(ctx, loc, NULL,
			"Type of size 0 is not a valid slice member");
		return &builtin_type_invalid;
	}
	assert(members->align != 0);

	struct type slice = {
		.storage = STORAGE_SLICE,
		.array = {
			.members = members,
			.length = SIZE_UNDEFINED,
		},
		.size = builtin_type_uintptr.size + 2 * builtin_type_size.size,
		.align = builtin_type_uintptr.align,
	};
	return type_store_lookup_type(ctx, &slice);
}

const struct type *
type_store_lookup_alias(struct context *ctx, struct ident *ident,
	struct ident *name, const struct type *secondary, bool exported)
{
	struct type type = {
		.storage = STORAGE_ALIAS,
		.alias.type = secondary,
		.alias.ident = ident,
		.alias.name = name,
		.alias.exported = exported,
	};
	return type_store_lookup_type(ctx, &type);
}

static struct type
lookup_tagged(struct context *ctx, struct location loc,
		struct type_tagged_union *tagged, bool valid)
{
	struct type ret = {
		.storage = STORAGE_TAGGED,
		.tagged = tagged_dup_tags(tagged),
	};
	tagged_init(ctx, &ret, loc, valid);
	return ret;
}

const struct type *
type_store_lookup_tagged(struct context *ctx, struct location loc,
		struct type_tagged_union *tagged)
{
	struct type temp = lookup_tagged(ctx, loc, tagged, true);
	switch (temp.tagged.len) {
	case 0:
		return &builtin_type_never;
	case 1:
		return temp.tagged.types[0];
	default:
		return type_store_lookup_type(ctx, &temp);
	}
}

const struct type *
type_store_lookup_tuple(struct context *ctx, struct location loc,
		struct type_tuple *values)
{
	struct type type = {
		.storage = STORAGE_TUPLE,
	};
	for (struct type_tuple *t = values; t; t = t->next) {
		if (t->type->storage == STORAGE_INVALID) {
			return &builtin_type_invalid;
		}
		if (t->type->storage == STORAGE_NULL) {
			error(ctx, loc, NULL,
				"Null type not allowed in this context");
			return &builtin_type_invalid;
		}
		t->type = lower_flexible(ctx, t->type, NULL);
		if (t->type->size == SIZE_UNDEFINED) {
			error(ctx, loc, NULL,
				"Type of undefined size is not a valid tuple member");
			return &builtin_type_invalid;
		}
		assert(t->type->align != ALIGN_UNDEFINED);

		if (t->type->align > type.align) {
			type.align = t->type->align;
		}
		t->offset = type.size;
		if (t->type->align != 0) {
			if (type.size % t->type->align != 0) {
				t->offset += t->type->align - type.size % t->type->align;
			}
			type.size = t->offset + t->type->size;
		}
	}
	type.tuple = *values;
	add_padding(&type.size, type.align);
	return type_store_lookup_type(ctx, &type);
}

const struct type *
type_store_lookup_enum(struct context *ctx, const struct ast_type *atype,
	bool exported)
{
	struct type type = {0};
	type.storage = STORAGE_ENUM;
	type.alias.ident = mkident(ctx, atype->alias, NULL);
	type.alias.name = atype->alias;
	type.alias.exported = exported;
	type.alias.type = builtin_type_for_storage(atype->_enum.storage);
	if (!type_is_integer(ctx, type.alias.type)
			&& type.alias.type->storage != STORAGE_RUNE) {
		error(ctx, atype->loc, NULL,
			"Enum storage must be an integer or rune");
		return &builtin_type_invalid;
	}
	type.size = type.alias.type->size;
	type.align = type.alias.type->size;
	return type_store_lookup_type(ctx, &type);
}

static void
expand_tagged(struct type_tagged_union *out, const struct type_tagged_union *in)
{
	for (size_t i = 0; i < in->len; i++) {
		if (in->types[i]->storage == STORAGE_TAGGED) {
			expand_tagged(out, &in->types[i]->tagged);
		} else {
			tagged_append(out, in->types[i]);
		}
	}
}

// Algorithm:
// - Deduplicate and collect nested unions
// - Remove never
// - Merge *type with nullable *type
// - If one of the types is null:
// 	- If there's more than one pointer type, error out
// 	- If there's one pointer type, make it nullable and drop the null
// 	- If there are no pointer types, keep the null
// - If the resulting union only has one type, return that type
// - Otherwise, if no types remain, return never
// - Otherwise, return a tagged union of all the selected types
const struct type *
type_store_reduce_result(struct context *ctx, struct location loc,
		struct type_tagged_union *in)
{
	if (!in || in->len == 0) {
		return &builtin_type_never;
	} else if (in->len == 1) {
		return in->types[0];
	}

	struct type_tagged_union expanded = { .types = NULL };
	expand_tagged(&expanded, in);
	struct type type = lookup_tagged(ctx, loc, &expanded, false);

	size_t ptr_index = 0;
	size_t nptrs = 0;
	bool have_null = false;
	size_t new_len = 0;
	for (size_t i = 0; i < type.tagged.len; i++) {
		const struct type *memb = type.tagged.types[i];
		if (memb->storage == STORAGE_NEVER || memb->storage == STORAGE_INVALID) {
			continue;
		}
		if (memb->storage == STORAGE_NULL) {
			have_null = true;
			continue;
		}
		if (memb->storage != STORAGE_POINTER) {
			type.tagged.types[new_len++] = memb;
			continue;
		}
		bool drop = false;
		for (size_t j = 0; j < i; j++) {
			const struct type *other = type.tagged.types[j];
			if (other->storage != STORAGE_POINTER) {
				continue;
			}
			// XXX: Why are we comparing IDs here?
			if (memb->pointer.referent->id != other->pointer.referent->id) {
				continue;
			}
			if (!memb->pointer.nullable && !other->pointer.nullable) {
				continue;
			}
			const struct type *_memb = type_store_lookup_pointer(ctx,
				loc, memb->pointer.referent, true);
			other = type_store_lookup_pointer(ctx, loc,
				other->pointer.referent, true);
			if (_memb == other) {
				type.tagged.types[j] = other;
				drop = true;
				break;
			}
		}
		if (!drop) {
			ptr_index = new_len;
			type.tagged.types[new_len++] = memb;
			nptrs++;
		}
	}
	type.tagged.len = new_len;

	if (have_null) {
		if (nptrs != 1) {
			error(ctx, loc, NULL,
				"Invalid result type (dangling or ambiguous null)");
			return &builtin_type_invalid;
		}
		// XXX: Flags?
		type.tagged.types[ptr_index] = type_store_lookup_pointer(ctx, loc,
			type.tagged.types[ptr_index]->pointer.referent, true);
	}

	return type_store_lookup_tagged(ctx, loc, &type.tagged);
}

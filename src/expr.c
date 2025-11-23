#include <math.h>
#include <string.h>
#include "expr.h"
#include "types.h"
#include "util.h"

uint32_t
expr_hash(const struct expression *expr)
{
	assert(expr && expr->type == EXPR_LITERAL);

	uint32_t hash = FNV1A_INIT;
	hash = fnv1a_u32(hash, type_hash(expr->result));
	// Add the storage a second time so that void and null expressions have
	// different hashes than their types.
	hash = fnv1a_u32(hash, expr->result->storage);

	enum type_storage storage = type_dealias(NULL, expr->result)->storage;

	switch (storage) {
	case STORAGE_DONE:
	case STORAGE_ERROR:
	case STORAGE_NOMEM:
	case STORAGE_NULL:
	case STORAGE_VOID:
	case STORAGE_UNDEFINED:
		break;
	case STORAGE_BOOL:
		hash = fnv1a(hash, expr->literal.bval);
		break;
	case STORAGE_F32:
	case STORAGE_F64:
	case STORAGE_FCONST:
		// TODO Consider how to hash different NaNs.
		assert(!isnan(expr->literal.fval));
		hash = fnv1a_u64(hash, expr->literal.uval);
		break;
	case STORAGE_I8:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_INT:
	case STORAGE_U8:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_UINT:
	case STORAGE_UINTPTR:
	case STORAGE_SIZE:
	case STORAGE_ENUM:
	case STORAGE_ICONST:
	case STORAGE_POINTER:
		// All of these have been cast up to 8 bytes, so the reinterpret
		// cast to uval is correct.
		hash = fnv1a_u64(hash, expr->literal.uval);
		break;
	case STORAGE_RCONST:
	case STORAGE_RUNE:
		hash = fnv1a_u32(hash, expr->literal.rune);
		break;
	case STORAGE_STRING:
		for (size_t i = 0; i < expr->literal.string.len; i++) {
			hash = fnv1a(hash, expr->literal.string.value[i]);
		}
		break;
	case STORAGE_SLICE: // Slice literals are stored as arrays.
	case STORAGE_ARRAY:
		for (struct array_literal *al = expr->literal.array;
				al; al = al->next) {
			hash = fnv1a_u32(hash, expr_hash(al->value));
		}
		break;
	case STORAGE_STRUCT:
	case STORAGE_UNION:
		for (struct struct_literal *sl = expr->literal._struct;
				sl; sl = sl->next) {
			hash = fnv1a_u32(hash, expr_hash(sl->value));
		}
		break;
	case STORAGE_TUPLE:
		for (struct tuple_literal *tl = expr->literal.tuple;
				tl; tl = tl->next) {
			hash = fnv1a_u64(hash, expr_hash(tl->value));
		}
		break;
	case STORAGE_TAGGED:
		hash = fnv1a_u32(hash, type_hash(expr->literal.tagged.tag));
		hash = fnv1a_u32(hash, expr_hash(expr->literal.tagged.value));
		break;
	case STORAGE_NEVER:
	case STORAGE_OPAQUE:
	case STORAGE_FUNCTION:
	case STORAGE_VALIST:
	case STORAGE_ALIAS: // handled above
		assert(0);
	}
	return hash;
}

bool
expr_equal(const struct expression *a, const struct expression *b)
{
	assert(a && a->type == EXPR_LITERAL);
	assert(b && b->type == EXPR_LITERAL);

	enum type_storage astor = type_dealias(NULL, a->result)->storage;
	enum type_storage bstor = type_dealias(NULL, b->result)->storage;
	if (astor != bstor) {
		return false;
	}

	switch (astor) {
	case STORAGE_DONE:
	case STORAGE_ERROR:
	case STORAGE_NOMEM:
	case STORAGE_NULL:
	case STORAGE_VOID:
	case STORAGE_UNDEFINED:
		return true;
	case STORAGE_BOOL:
		return a->literal.bval == b->literal.bval;
	case STORAGE_F32:
	case STORAGE_F64:
	case STORAGE_FCONST:
		// TODO Consider how to compare different NaNs.
		assert(!isnan(a->literal.fval));
		assert(!isnan(b->literal.fval));
		return a->literal.fval == b->literal.fval;
	case STORAGE_I8:
	case STORAGE_I16:
	case STORAGE_I32:
	case STORAGE_I64:
	case STORAGE_INT:
	case STORAGE_U8:
	case STORAGE_U16:
	case STORAGE_U32:
	case STORAGE_U64:
	case STORAGE_UINT:
	case STORAGE_UINTPTR:
	case STORAGE_SIZE:
	case STORAGE_ENUM:
	case STORAGE_ICONST:
	case STORAGE_POINTER:
		// All of these have been cast up to 8 bytes, so the reinterpret
		// cast to uval is correct.
		return a->literal.uval == b->literal.uval;
	case STORAGE_RCONST:
	case STORAGE_RUNE:
		return a->literal.rune == b->literal.rune;
	case STORAGE_STRING:
		if (a->literal.string.len != b->literal.string.len) {
			return false;
		}
		return memcmp(a->literal.string.value, b->literal.string.value,
				a->literal.string.len) == 0;
	case STORAGE_SLICE: // Slice literals are stored as arrays.
	case STORAGE_ARRAY:;
		struct array_literal *aa = a->literal.array;
		struct array_literal *ba = b->literal.array;
		while (aa && ba) {
			if (!expr_equal(aa->value, ba->value)) {
				return false;
			}
			aa = aa->next;
			ba = ba->next;
		}
		return true;
	case STORAGE_STRUCT:
	case STORAGE_UNION:;
		struct struct_literal *as = a->literal._struct;
		struct struct_literal *bs = b->literal._struct;
		while (as && bs) {
			if (!expr_equal(as->value, bs->value)) {
				return false;
			}
			as = as->next;
			bs = bs->next;
		}
		return true;
	case STORAGE_TUPLE:;
		struct tuple_literal *at = a->literal.tuple;
		struct tuple_literal *bt = b->literal.tuple;
		while (at && bt) {
			if (!expr_equal(at->value, bt->value)) {
				return false;
			}
			at = at->next;
			bt = bt->next;
		}
		return true;
	case STORAGE_TAGGED:
		return a->literal.tagged.tag == b->literal.tagged.tag
			&& expr_equal(a->literal.tagged.value, b->literal.tagged.value);
	case STORAGE_NEVER:
	case STORAGE_OPAQUE:
	case STORAGE_FUNCTION:
	case STORAGE_VALIST:
	case STORAGE_ALIAS: // handled above
		assert(0);
	}
	assert(0); // Unreachable
}

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "expr.h"
#include "identifier.h"
#include "scope.h"
#include "util.h"

static uint32_t
name_hash(uint32_t init, const struct ident *ident)
{
	return fnv1a_s(init, ident->name);
}

struct scope *
scope_push(struct scope **stack, enum scope_class class)
{
	struct scope *new = xcalloc(1, sizeof(struct scope));
	new->class = class;
	new->results.types = NULL;
	new->next = &new->objects;
	new->parent = *stack;
	*stack = new;
	return new;
}

struct scope *
scope_pop(struct scope **stack)
{
	struct scope *prev = *stack;
	assert(prev);
	*stack = prev->parent;
	return prev;
}

struct scope *
scope_lookup_class(struct scope *scope, enum scope_class class)
{
	while (scope) {
		if (scope->class == class) {
			break;
		}
		scope = scope->parent;
	}
	return scope;
}

struct scope *
scope_lookup_label(struct scope *scope, const char *label)
{
	while (scope) {
		if (scope->label && strcmp(scope->label, label) == 0) {
			break;
		}
		scope = scope->parent;
	}
	return scope;
}

void
scope_free(struct scope *scope)
{
	if (!scope) {
		return;
	}

	struct scope_object *obj = scope->objects;
	while (obj) {
		struct scope_object *next = obj->lnext;
		free(obj);
		obj = next;
	}

	free(scope);
}

void
scope_free_all(struct scopes *scopes)
{
	while (scopes) {
		struct scopes *next = scopes->next;
		scope_free(scopes->scope);
		free(scopes);
		scopes = next;
	}
}

struct scope_object *
scope_insert(struct scope *scope, enum object_type otype,
	struct ident *ident, struct ident *name, const struct type *type,
	struct expression *value)
{
	assert(otype == O_SCAN || !type != !value);
	struct scope_object *obj = xcalloc(1, sizeof(struct scope_object));
	obj->ident = ident;
	obj->name = name;
	obj->otype = otype;
	if (type) {
		obj->type = type;
	} else if (value) {
		obj->value = value;
		assert(otype == O_CONST);
		assert(value->type == EXPR_LITERAL);
	}
	flexible_refer(type, &obj->type);

	// Linked list
	*scope->next = obj;
	scope->next = &obj->lnext;

	// Hash map
	uint32_t hash = name_hash(FNV1A_INIT, obj->name);
	struct scope_object **bucket = &scope->buckets[hash % SCOPE_BUCKETS];
	if (*bucket) {
		obj->mnext = *bucket;
	}
	*bucket = obj;
	return obj;
}

struct scope_object *
scope_lookup(struct scope *scope, struct ident *ident)
{
	uint32_t hash = name_hash(FNV1A_INIT, ident);
	struct scope_object *bucket = scope->buckets[hash % SCOPE_BUCKETS];
	while (bucket) {
		if (bucket->name == ident) {
			return bucket;
		}
		bucket = bucket->mnext;
	}
	if (scope->parent) {
		return scope_lookup(scope->parent, ident);
	}
	return NULL;
}

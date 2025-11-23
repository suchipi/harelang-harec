#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "identifier.h"
#include "util.h"

bool
ident_equal(const struct ident *a, const struct ident *b)
{
	while (a && b) {
		if (strcmp(a->name, b->name)) {
			return false;
		}
		a = a->ns;
		b = b->ns;
	}
	return !a && !b;
}

uint32_t
ident_hash(uint32_t init, const struct ident *ident)
{
	init = fnv1a_s(init, ident->name);
	init = fnv1a(init, 0);
	if (ident->ns != NULL) {
		init = ident_hash(init, ident->ns);
	}
	return init;
}

static void
ident_unparse_ex(const struct ident *id, const char *delim,
	size_t delimlen, char **buf, size_t *len, size_t *cap)
{
	const struct ident *ident = id;
	if (ident->ns != NULL) {
		ident_unparse_ex(ident->ns, delim,
			delimlen, buf, len, cap);
		append_buffer(buf, len, cap, delim, delimlen);
	}
	size_t namelen = strlen(ident->name);
	append_buffer(buf, len, cap, ident->name, namelen);
}

char *
ident_unparse(const struct ident *ident)
{
	size_t len = 0;
	size_t cap = strlen(ident->name) + 1;
	char *buf = xcalloc(cap, sizeof(char));
	ident_unparse_ex(ident, "::", 2, &buf, &len, &cap);
	return buf;
}

int
ident_unparse_static(const struct ident *ident, char *buf)
{
	if (ident->ns != NULL) {
		int prefix = ident_unparse_static(ident->ns, buf);
		int n = snprintf(&buf[prefix], IDENT_BUFSIZ - prefix,
				"::%s", ident->name);
		n += prefix;
		assert(n < IDENT_BUFSIZ);
		return n;
	}
	int n = snprintf(buf, IDENT_BUFSIZ, "%s", ident->name);
	assert(n < IDENT_BUFSIZ);
	return n;
}

const char *
ident_to_sym(struct intern_table *itbl, const struct ident *ident)
{
	size_t len = 0;
	size_t cap = strlen(ident->name) + 1;
	char *buf = xcalloc(cap, sizeof(char));
	ident_unparse_ex(ident, ".", 1, &buf, &len, &cap);
	return intern_owned(itbl, buf);
}

#define SZ 0x2000
static_assert((SZ & (SZ - 1)) == 0, "SZ must be a power of 2");

static const char *
intern_str(struct intern_table *itbl, char *s, bool owned)
{
	uint32_t h = fnv1a_s(FNV1A_INIT, s);
	struct bucket *b = &itbl->sbuckets[h & (SZ - 1)];
	for (size_t i = 0; i < b->sz; i++) {
		if (!strcmp(b->ids[i], s)) {
			if (owned) {
				free(s);
			}
			return b->ids[i];
		}
	}
	if (!owned) {
		s = xstrdup(s);
	}
	if (b->sz == b->cap) {
		if (b->cap == 0) {
			b->cap = 4;
		}
		b->cap *= 2;
		b->ids = xrealloc(b->ids, b->cap * sizeof b->ids[0]);
	}
	return b->ids[b->sz++] = s;
}

const char *
intern_owned(struct intern_table *itbl, char *s)
{
	return intern_str(itbl, s, true);
}

const char *
intern_copy(struct intern_table *itbl, const char *s)
{
	return intern_str(itbl, (char *)s, false);
}

void
intern_init(struct intern_table *itbl)
{
	itbl->sbuckets = xcalloc(SZ, sizeof (struct bucket));
	itbl->ibuckets = xcalloc(SZ, sizeof (struct bucket));
}

struct ident *
intern_ident(struct intern_table *itbl, const char *name, struct ident *ns)
{
	struct ident ident = { .name = name, .ns = ns };
	uint32_t h = ident_hash(FNV1A_INIT, &ident);
	struct bucket *b = &itbl->ibuckets[h & (SZ - 1)];
	for (size_t i = 0; i < b->sz; i++) {
		const struct ident *id1 = b->ids[i], *id2 = &ident;
		for (; id1 && id2 && id1 != id2; id1 = id1->ns, id2 = id2->ns) {
			if (id1->name != id2->name) {
				break;
			}
		}
		if (id1 == id2) {
			return b->ids[i];
		}
	}
	if (b->sz == b->cap) {
		if (b->cap == 0) {
			b->cap = 4;
		}
		b->cap *= 2;
		b->ids = xrealloc(b->ids, b->cap * sizeof b->ids[0]);
	}
	struct ident *new = xcalloc(1, sizeof (struct ident));
	*new = ident;
	return b->ids[b->sz++] = new;
}

struct ident *
intern_name(struct intern_table *itbl, const char *name)
{
	return intern_ident(itbl, name, NULL);
}

#ifndef HARE_IDENTIFIER_H
#define HARE_IDENTIFIER_H
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Maximum length of an identifier, as the sum of the lengths (excluding NUL
// terminators) of its parts plus one for each namespace deliniation.
//
// In other words, the length of "a::b::c" is 5.
#define IDENT_MAX 255

// Minimum buffer size needed to store an unparsed identifier, including the
// terminating NUL byte.
#define IDENT_BUFSIZ (IDENT_MAX / 2 + IDENT_MAX + 1)

struct ident {
	const char *name;
	struct ident *ns;
};

struct identifiers {
	struct ident *ident;
	struct identifiers *next;
};

struct bucket {
	void **ids;
	size_t sz;
	size_t cap;
};

struct intern_table {
	struct bucket *sbuckets;
	struct bucket *ibuckets;
};

bool ident_equal(const struct ident *a, const struct ident *b);
uint32_t ident_hash(uint32_t init, const struct ident *ident);
char *ident_unparse(const struct ident *ident);
int ident_unparse_static(const struct ident *ident, char *buf);
const char *ident_to_sym(struct intern_table *itbl, const struct ident *ident);

void intern_init(struct intern_table *itbl);

const char *intern_copy(struct intern_table *itbl, const char *s);
const char *intern_owned(struct intern_table *itbl, char *s);

struct ident *intern_ident(struct intern_table *itbl,
		const char *name, struct ident *ns);
struct ident *intern_name(struct intern_table *itbl, const char *name);

#endif

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "check.h"
#include "identifier.h"
#include "lex.h"
#include "mod.h"
#include "parse.h"
#include "scope.h"
#include "util.h"

// unfortunately necessary since this is used in an array declaration, and we
// don't want a VLA
#define strlen_HARE_TD_ (sizeof("HARE_TD_") - 1)

struct scope *
module_resolve(struct context *ctx, const struct ast_global_decl *defines,
	struct ident *ident)
{
	uint32_t hash = ident_hash(FNV1A_INIT, ident);
	struct modcache **bucket = &ctx->modcache[hash % MODCACHE_BUCKETS];
	for (; *bucket; bucket = &(*bucket)->next) {
		if ((*bucket)->ident == ident) {
			return (*bucket)->scope;
		}
	}

	struct lexer lexer = {0};
	struct ast_unit aunit = {0};

	// env = "HARE_TD_foo::bar::baz"
	char env[strlen_HARE_TD_ + IDENT_BUFSIZ] = "HARE_TD_";
	ident_unparse_static(ident, &env[strlen_HARE_TD_]);

	char *path = getenv(env);
	if (!path) {
		xfprintf(stderr, "Could not open module '%s': typedef variable $%s not set\n",
			&env[strlen_HARE_TD_], env);
		exit(EXIT_USER);
	}

	FILE *f = fopen(path, "r");
	if (!f) {
		xfprintf(stderr, "Could not open module '%s' for reading from %s: %s\n",
			&env[strlen_HARE_TD_], path, strerror(errno));
		exit(EXIT_ABNORMAL);
	}

	const char *old = sources[0];
	sources[0] = path;
	lex_init(&lexer, f, 0, ctx->itbl);
	parse(&lexer, &aunit.subunits);
	lex_finish(&lexer);

	// TODO: Free unused bits
	struct unit u = {0};
	struct scope *scope = check_internal(ctx->store, ctx->modcache,
		ctx->is_test, ctx->mainsym, ctx->mainident, defines, &aunit,
		&u, ctx->itbl, true);

	sources[0] = old;
	bucket = &ctx->modcache[hash % MODCACHE_BUCKETS];
	struct modcache *item = xcalloc(1, sizeof(struct modcache));
	item->ident = ident;
	item->scope = scope;
	item->next = *bucket;
	*bucket = item;
	return scope;
}

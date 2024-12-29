#ifndef HARE_MOD_H
#define HARE_MOD_H

struct ast_global_decl;
struct context;
struct ident;

struct scope *module_resolve(struct context *ctx,
	const struct ast_global_decl *defines, struct ident *ident);

#endif

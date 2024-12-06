export fn toutf8(s: str) []u8 = *(&s: *[]u8);

fn alloc_cstr(s: str) *u8 = {
	let c: []u8 = alloc([], len(s) + 1);
	append(c, *(&s: *[]u8)...);
	append(c, 0);
	return *(&c: **u8);
};

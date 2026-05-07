export fn strcmp(a: str, b: str) bool = {
	if (len(a) != len(b)) {
		return false;
	};
	let ln = len(a);
	let a = toutf8(a): *[*]u8, b = toutf8(b): *[*]u8;
	for (let i = 0z; i < ln; i += 1) {
		if (a[i] != b[i]) {
			return false;
		};
	};
	return true;
};

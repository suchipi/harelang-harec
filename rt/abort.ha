fn write_stderr(s: str) size = write(2, *(&s: **opaque), len(s));

export @symbol("rt.abort") fn _abort(
	path: *str,
	line: u64,
	col: u64,
	msg: str,
) void = {
	write_stderr("Abort: ");
	write_stderr(*path);
	write_stderr(":");
	write_stderr(u64tos(line));
	write_stderr(":");
	write_stderr(u64tos(col));
	write_stderr(": ");
	write_stderr(msg);
	write_stderr("\n");
	kill(getpid(), SIGABRT);
};

// See harec:include/expr.h enum fixed_aborts
const reasons: [_]str = [
	"slice or array access out of bounds",	// 0
	"type assertion failed",		// 1
	"unreachable code",			// 2
	"slice allocation capacity smaller than initializer",	// 3
	"assertion failed",			// 4
	"error occurred",			// 5
];

export fn abort_fixed(path: *str, line: u64, col: u64, i: u64) void = {
	_abort(path, line, col, reasons[i]);
};

fn u64tos(u: u64) str = {
	static let buf: [20]u8 = [0...]; // len("18446744073709551615")
	let sl = buf[..0];
	if (u == 0) {
		static append(sl, '0')!;
	};
	for (u > 0) {
		static append(sl, (u % 10): u8 + '0')!;
		u /= 10;
	};
	for (let s = 0z, e = len(sl) - 1; s < e) {
		let tmp = sl[s];
		sl[s] = sl[e];
		sl[e] = tmp;
		s += 1;
		e -= 1;
	};
	return *(&sl: *str);
};

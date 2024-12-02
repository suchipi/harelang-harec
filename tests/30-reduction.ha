use rt::{compile, status, toutf8};

fn assert_fail(expr: str) void = {
	let buf: [1024]u8 = [0...];
	let buf = buf[..0];
	static append(buf, toutf8("export fn main() void = {\n")...);
	static append(buf, toutf8(expr)...);
	static append(buf, toutf8(";\n};")...);
	compile(status::CHECK, *(&buf: *str))!;
};

export fn main() void = {
	// format:
	// let x = &expr;
	// let x: *type = x;

	let x = &(if (true) 0i else void);
	let x: *(int | void) = x;

	let x = &match (0u8: (u8 | u16 | u32 | u64)) {
	case u8 =>
		yield null: *int;
	case u16 =>
		yield null: nullable *int;
	case u32 =>
		yield null;
	case u64 =>
		yield;
	};
	let x: *(nullable *int | void) = x;

	let x = &switch (0) {
	case 42 =>
		yield null: *int;
	case 69 =>
		yield null: nullable *int;
	case 1337 =>
		yield null;
	case =>
		yield;
	};
	let x: *(nullable *int | void) = x;

	// if, match, and switch all use the same code for reduction, so we
	// don't need to rigorously test all three

	let x = &(if (true) null: *int else null);
	let x: *nullable *int = x;

	let x = &(if (true) null: *int else null: nullable *int);
	let x: *nullable *int = x;

	let x = &{
		if (true) yield;
		yield 0;
	};
	let x: *(int | void) = x;

	assert_fail("if (true) null "
		"else if (true) null: *int "
		"else null: *opaque");
	assert_fail("if (true) null else void");
	assert_fail("if (true) null: *int else if (true) null");

	// However, literals behave differently in if vs switch/match

	let x = &(if (true) 0 else if (true) 1 else 2);
	let x: *int = x;

	let x = &(if (true) 0 else 9223372036854775807);
	let x: *(int | i64) = x;

	let x = &(if (true) 0 else 0z);
	let x: *(int | size) = x;

	let x = &(if (true) 0 else void);
	let x: *(int | void) = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case 1 =>
		yield 1;
	case =>
		yield 2;
	};
	let x: *int = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case =>
		yield 9223372036854775807;
	};
	let x: *(int | i64) = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case =>
		yield 0z;
	};
	let x: *(int | size) = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case =>
		yield;
	};
	let x: *(int | void) = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case 1 =>
		yield 1z;
	case =>
		yield 2u32;
	};
	let x: *(int | size | u32) = x;

	let x = &switch (0) {
	case 0 =>
		yield 0;
	case 1 =>
		yield 1i;
	case =>
		yield 9223372036854775807;
	};
	let x: *(int | i64) = x;

	let x = &{
		for (false) yield 42;
	};
	let x: *(int | void) = x;
};

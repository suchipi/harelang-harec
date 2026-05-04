use rt::{compile, status, slice};

type my_struct = struct {
	x: int,
	y: int,
};

type my_struct_ptr = *my_struct;
type nomem_alias = nomem;

type my_int = int;
type my_u32 = u32;

fn allocation() void = {
	let x = alloc(1234)!;
	assert(*x == 1234);
	free(x);

	let y: (*int | nomem) = alloc(1234);
	if (!(y is nomem)) {
		assert(*(y as *int) == 1234);
	};
	free(y as *int);

	let z: my_struct_ptr = alloc(my_struct {
		x = 42,
		y = 69,
	})!;
	assert(z.x == 42 && z.y == 69);
	free(z);

	let w: *my_int = alloc(1234)!;
	assert(*w == 1234);
	free(w);

	let a: *const my_u32 = alloc(1234u32)!;
	assert(*a == 1234);
	free(a);

	let q: *int = alloc(@undefined)!;
	*q = 1337;
	free(q);
};

fn failure() (void | nomem_alias) = {
	let x = alloc([1u8...], 500000000000000); // 500 TB
	assert(x is nomem);

	let sl = *(&slice {
		data = 0xdeaddead: uintptr: *opaque,
		length = 500000000000000,
		capacity = 500000000000000,
	}: *[]u8);

	let x = alloc(sl...);
	assert(x is nomem);

	let x: (*[500000000000000]u8 | nomem) = alloc([1...]);
	assert(x is nomem);

	let x: (*[500000000000000]u8 | nomem) = alloc([1...])?;
	abort(); // unreachable
};

fn assignment() void = {
	let x = alloc(1234)!;
	*x = 4321;
	assert(*x == 4321);
	free(x);
};

fn double_pointer() void = {
	let x = alloc(1234)!;
	let y = alloc(x)!;
	*x = 4321;
	assert(**y == 4321);
	**y = 1337;
	assert(*x == 1337);
	free(y);
	free(x);
};

fn double_alloc() void = {
	let x = alloc(1234)!;
	let y = alloc(4321)!;
	assert(x != y && *x != *y);
	free(x);
	free(y);
};

type aslice = []int;
type aarray = [3]int;

fn array() void = {
	let aa: *aarray = alloc([0...])!;
	free(aa);
	let aa: *aarray = alloc([0...])!;
	free(aa);
	let aa: *aarray = alloc([0...]: aarray)!;
	free(aa);
	let aa: *aarray = alloc([0...]: aarray)!;
	free(aa);

	let x: *[24]int = alloc([1, 2...])!;

	assert(len(x) == 24);
	assert(x[0] == 1);
	for (let i = 1z; i < len(x); i += 1) {
		assert(x[i] == 2);
	};
	free(x);
};

fn slice_allocation() void = {
	let x: aslice = alloc([1, 2, 3]: aarray, 10)!;
	assert(len(x) == 3);
	for (let i = 0z; i < len(x); i += 1) {
		assert(x[i] == (i + 1): int);
	};
	free(x);

	let y: []int = alloc([1, 2, 3])!;
	assert(len(x) == 3);
	for (let i = 0z; i < len(y); i += 1) {
		assert(y[i] == (i + 1): int);
	};
	free(y);

	let z: []int = [];
	let p = &z: *struct {
		data: nullable *[*]int,
		length: size,
		capacity: size,
	};
	assert(p.data == null && p.length == 0 && p.capacity == 0);

	let x: []int = alloc([1, 2, 3...], 42)!;
	defer free(x);
	assert(x[0] == 1);
	assert(x[1] == 2);
	assert(x[2] == 3);
	for (let i = 2z; i < len(x); i += 1) {
		assert(x[i] == 3);
	};

	// ensure capacity is cast to size correctly
	let a: u32 = 4;
	let y: []u64 = alloc([1...], a)!;
	defer free(y);
	assert(len(y) == 4 && y[0] == 1 && y[3] == 1);
};

fn slice_copy() void = {
	let x: []int = [1, 2, 3];

	let p: []int = alloc(x...)!;
	defer free(p);
	assert(p: *[*]int != x: *[*]int);
	assert(len(p) == len(x));
	for (let i = 0z; i < len(p); i += 1) {
		assert(p[i] == x[i]);
	};

	let q: *[]int = alloc(x)!;
	defer free(q);
	assert((*q): *[*]int == x: *[*]int);

	let r: []int = alloc([1, 2, 3]...)!;
	defer free(r);
	assert(len(x) == len(r));
	for (let i = 0z; i < len(x); i += 1) {
		assert(x[i] == r[i]);
	};
};

fn string() void = {
	let x = struct {
		data: *[3]int = alloc([1, 2, 3])!,
		length: size = 3,
		capacity: size = 3,
	};
	let y = *(&x: *str);
	assert(len(y) == 3);
	free(y);
};

fn _null() void = {
	let x: nullable *int = null;
	free(x);
	free(null);
};

fn aliases() void = {
	compile(status::CHECK,
		"fn test() void = { let x: (*u32 | *u64 | nomem) = alloc(123); };"
	)!;
};

export fn main() void = {
	assert(size(nomem) == 0);

	assignment();
	assert(failure() is nomem_alias);
	allocation();
	double_pointer();
	double_alloc();
	array();
	slice_allocation();
	slice_copy();
	string();
	_null();
	aliases();
};

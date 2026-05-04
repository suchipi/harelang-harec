use rt::{compile, status};

type int_alias = int;
type tagged_alias = (int | str);
type tuple_alias = (str, int);

type slice_alias = []int_alias;
type array_alias = [4]int_alias;

fn scope() void = {
	let x = 0;
	for (let i = 1; i == 1; i += 1) {
		for (true) {
			assert(x == 0);
			assert(i == 1);
			break;
		};
	};
	compile(status::CHECK, "fn test() void = { for (true) { let x = 10; break; }; x; };")!;
	// To make sure that the afterthought is part of the loop's scope
	for (let i = 0; true; (if (true) { break; })) true;
};

fn conditional() void = {
	let i = 1;
	for (i < 10) {
		i *= 2;
	};
	assert(i == 16);
};

fn afterthought() void = {
	let i = 1;
	for (i < 5; i += 1) {
		i *= 2;
	};
	assert(i == 7);
};

fn binding() void = {
	let x = 0;
	for (let i = 0; i < 10; i += 1) {
		i *= 2;
		x += 1;
	};
	assert(x == 4);
};

fn _break() void = {
	let x = 0;
	for (let i = 0; i < 1; i += 1) {
		let j = 0;
		for (j < 10) {
			j += 1;
			if (j == 5) {
				break;
			};
		};
		assert(j == 5);
		x += 1;
	};
	assert(x == 1);
};

fn break_value() void = {
	let x = for (let i = 0; i < 1; i += 1) {
		if (true) break 5;
	};
	assert(x as int == 5);

	let x = for (let i = 0; i < 1; i += 1) {
		if (false) break 5;
	};
	assert(x is void);

	let x = for (let i = 0; i < 1; break 5) void;
	assert(x as int == 5);

	for (let i = 0; i < 1; i += 1) {
		if (true) { break 5; };
	};

	let x = for (let i = 0; i < 1; i += 1) {
		if (true) break "hi" else break 5;
	};
	assert(x as str == "hi");

	let x = for :outer (let i = 0; i < 1; i += 1) {
		for (let j = 0; j < 1; j += 1) break :outer, 5;
	};
	assert(x as int == 5);

	let x = for (let x .. [1, 2, 3, 4]) {
		if (x == 3) break x;
	};
	assert(x as int == 3);

	let x: (size | void) = for (let i = 0; i < 1; i += 1) {
		break 4;
	};
	assert(x as size == 4z);
};

fn _continue() void = {
	let finished = false;
	let x = 0;
	for (!finished) {
		for (let i = 0; i < 10; i += 1) {
			if (i == 5) {
				continue;
			};
			assert(i != 5);
		};
		finished = true;
		x += 1;
	};
	assert(x == 1);
};

fn label() void = {
	let i = 0;
	for :outer (i < 10) {
		for :inner (let j = 0; j < 7; j += 1) {
			i += 1;
			if (j == 6) {
				for (let k = 0; k < 5; k += 1) {
					if (k == 2) {
						continue :inner;
					};
					assert(k < 2);
				};
			};
			assert(j != 6);
			if (i > 7) {
				break :outer;
			};
		};
	};
	assert(i == 8);
	compile(status::CHECK, "fn test() void = { for :foo (true) { break :bar; }; };")!;
	compile(status::CHECK, "fn test() void = { for (true) { break :bar; }; };")!;
	compile(status::CHECK, "fn test() void = { break :bar; };")!;
	compile(status::CHECK, "fn test() void = :foo { break :foo; };")!;
	compile(status::CHECK, "fn test() void = { for :foo (true) { yield :foo; }; };")!;
	compile(status::CHECK, "fn test() void = :foo { for :foo (true) { yield :foo; }; };")!;
	compile(status::CHECK, "fn test() void = for :foo (true) :foo { break :foo; };")!;
};

type abool = bool;

fn alias() void = {
	for (true: abool) {
		return;
	};
};

fn result() void = {
	for (true) break;
	for :loop (true) {
		for (true) break :loop;
	};
	let integer = switch (0) {
	case 0 => yield 0;
	case => for (true) void;
	};
	assert(integer == 0);
};

fn foreach_next() (int | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return counter;
	};
	return done;
};

fn foreach_next_alias() (int_alias | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return counter;
	};
	return done;
};

fn foreach_next_void() (void | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return void;
	};
	return done;
};

fn foreach_tuple() ((str, int) | done) = {
	let pairs = [
		("Hello", 1),
		("World", 2),
		("!", 3),
	];
	static let counter = 0;

	if (counter < 3) {
		counter += 1;
		return pairs[counter - 1];
	};
	return done;
};

fn foreach_tuple_alias() (tuple_alias | done) = {
	let pairs = [
		("Hello", 1),
		("World", 2),
		("!", 3),
	];
	static let counter = 0;

	if (counter < 3) {
		counter += 1;
		return pairs[counter - 1];
	};
	return done;
};

fn foreach_large() ([1024]int | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return [12...];
	};
	return done;
};

fn foreach_tagged() (int | str | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return if (counter % 2 == 0) counter else "";
	};
	return done;
};

fn foreach_tagged_alias() (tagged_alias | done) = {
	static let counter = 0;
	if (counter < 4) {
		counter += 1;
		return if (counter % 2 == 0) counter else "";
	};
	return done;
};

fn for_each() void = {
	let array = [1, 2, 3];
	let slice: []int = [1, 2, 3];

	let pairs = [
		("Hello", 1),
		("World", 2),
		("!", 3),
	];

	let counter = 1;
	for (let x .. []: []int) {
		counter += 1;
	};
	assert(counter == 1);

	let counter = 1;
	for (let x &.. []: []int) {
		counter += 1;
	};
	assert(counter == 1);

	let counter = 1;
	for (let x .. array) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x .. slice) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x .. &slice) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1u32;
	for (let x: u32 .. [1, 2, 3]) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 0;
	for (let (string, count) .. pairs) {
		assert(string == pairs[counter].0);
		assert(count == pairs[counter].1);
		counter += 1;
	};
	assert(counter == 3);

	let counter = 0;
	for (let (string, count) .. pairs[..]) {
		assert(string == pairs[counter].0);
		assert(count == pairs[counter].1);
		counter += 1;
	};
	assert(counter == 3);

	let counter = 0z;
	for (let _ .. array) {
		counter += 1;
	};
	assert(counter == len(array));

	let counter = 0z;
	for (let _ .. slice) {
		counter += 1;
	};
	assert(counter == len(array));

	let counter = 1u32;
	for (let x: *u32 &.. [1, 2, 3]) {
		assert(*x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x &.. array) {
		assert(*x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x &.. slice) {
		assert(*x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x: *int &.. array) {
		assert(*x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x: *int &.. slice) {
		assert(*x == counter);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 0z;
	for (let _ &.. array) {
		counter += 1;
	};
	assert(counter == len(array));

	let counter = 0z;
	for (let _ &.. slice) {
		counter += 1;
	};
	assert(counter == len(array));

	let counter = 1;
	for (let x => foreach_next()) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 0;
	for (let _ => if (counter < 4) counter += 1 else done) void;
	assert(counter == 4);

	let counter = 1;
	for (let x => foreach_next_alias()) {
		assert(x == counter);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 0;
	for (let (string, count) => foreach_tuple()) {
		assert(string == pairs[counter].0);
		assert(count == pairs[counter].1);
		counter += 1;
	};
	assert(counter == 3);

	let counter = 0;
	for (let (string, count) => foreach_tuple_alias()) {
		assert(string == pairs[counter].0);
		assert(count == pairs[counter].1);
		counter += 1;
	};
	assert(counter == 3);

	let counter = 1;
	for (let x => foreach_tagged()) {
		if (counter % 2 == 0) {
			assert(x as int == counter);
		} else {
			assert(x as str == "");
		};
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let x => foreach_tagged_alias()) {
		if (counter % 2 == 0) {
			assert(x as int == counter);
		} else {
			assert(x as str == "");
		};
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let (x, y) .. [(void, 1), (void, 2), (void, 3)]) {
		assert(counter == y);
		counter += 1;
	};
	assert(counter == 4);

	for (let x => foreach_next_void()) {
		x;
	};

	let counter = 1;
	for (let x => foreach_large()) {
		for (let y .. x) {
			assert(y == 12);
		};
		counter += 1;
	};
	assert(counter == 5);

	let test_slice: slice_alias = [1, 1, 1];

	let counter = 1;
	for (let x .. test_slice) {
		assert(x == 1);
		counter += 1;
	};
	assert(counter == 4);

	let counter = 1;
	for (let x &.. test_slice) {
		assert(*x == 1);
		counter += 1;
	};
	assert(counter == 4);

	let test_array: array_alias = [2, 2, 2, 2];

	let counter = 1;
	for (let x .. test_array) {
		assert(x == 2);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let x &.. test_array) {
		assert(*x == 2);
		counter += 1;
	};
	assert(counter == 5);

	// pointer to alias of array type:
	let test_array_ref = &test_array;
	let counter = 1;
	for (let x &.. test_array_ref) {
		assert(*x == 2);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let x &.. &test_array) {
		assert(*x == 2);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let x &.. &(&(&test_array))) {
		assert(*x == 2);
		counter += 1;
	};
	assert(counter == 5);

	let counter = 1;
	for (let x => done: (int | done)) {
		counter += 1;
	};
	assert(counter == 1);

	// No unpacking by reference
	compile(status::CHECK, "fn test() void = {
		let pairs = [(1, 2), (3, 4), (5, 6)];
		for (let (x, y) &.. pairs) {
			x;
		};
	};")!;

	compile(status::PARSE, "fn test() void = { for (static let i = 0; i < 4; i += 1) { i; } };")!;
	compile(status::CHECK, "type done_alias = done; fn next() (int | done_alias | str | done) = done; fn test() void = { for (let x => next()) { x; }; };")!;
	compile(status::CHECK, "fn test() void = { let slice: []int = []; for (let x .. slice) { delete(slice[0]); };};")!;
	compile(status::CHECK, "fn test() void = { let slice: []int = []; for (let x .. slice) { append(slice, 1); };};")!;
	compile(status::CHECK, "fn test() void = { let slice: []int = []; for (let x .. slice) { insert(slice[0], 1); };};")!;
	compile(status::CHECK, "fn test() void = { let slice: []int = []; for (let x .. slice) { free(slice); };};")!;
};

fn next() ((int, int) | done) = (4, 2);

fn for_else() void = {
	for (let i = 0; i < 10; i += 1) {
		if (i == 3) break;
	} else abort();

	let x = for (let i = 0; i < 10; i += 1) void else true;
	assert(x);

	let x = for (let i = 0; i < 10; i += 1) break else true;
	assert(x is void);

	let found = for (let i = 0; i < 10; i += 1) {
		if (i == 3) break true;
	} else false;
	assert(found);

	let found = for (let i = 0; i < 10; i += 1) {
		if (i == 13) break true;
	} else false;
	assert(!found);

	let found = for (let x .. [1, 2, 3, 4]) {
		if (x == 3) break true;
	} else false;
	assert(found);

	let found = for (let x .. [1, 2, 3, 4]) {
		if (x == 5) break true;
	} else false;
	assert(!found);

	let x = 0;
	let v = for (true) {
		x += 1;
		if (x == 3) break true;
	} else 5;
	assert(v);

	let x = for (true) if (true) break 1 else break 2;
	assert(x == 1);

	// This form tests gen_expr, instead of gen_expr_with.
	assert(for (let i .. [1, 2]) { if (i == 2) break true; } else false);
};

export fn main() void = {
	scope();
	conditional();
	afterthought();
	binding();
	_break();
	break_value();
	_continue();
	label();
	alias();
	result();
	for_each();
	for_else();
};

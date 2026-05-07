type xsw_usage = struct {
	xsu_total: u64,
	xsu_avail: u64,
	xsu_used: u64,
	xsu_pagesize: u32,
	xsu_encrypted: u32,
};

// Cached upper bound for segmalloc requests (physical RAM + total swap, in
// bytes). 0 = uninitialized; populated on first segmalloc call.
let cached_max_segmalloc: size = 0;

// Allocates a segment.
fn segmalloc(n: size) nullable *opaque = {
	if (n > max_segmalloc()) return null;
	let p: *opaque = mmap(null, n,
		PROT_READ | PROT_WRITE,
		MAP_PRIVATE | MAP_ANON, -1, 0);
	return if (p == MAP_FAILED) null else p;
};

def MAP_FAILED: *opaque = -1: uintptr: *opaque;

// Frees a segment allocated with segmalloc.
fn segfree(p: *opaque, s: size) int = munmap(p, s);

// Returns the largest allocation segmalloc will honor on this system.
//
// macOS's mmap returns a valid virtual address even for absurdly large
// requests (no bounded overcommit check at the syscall level), so a naive
// segmalloc would hand back pointers that SIGBUS on first touch. To match
// the nomem-RFC contract that a null return from segmalloc means honest
// capacity exhaustion, query physical RAM + total swap once via sysctl and
// refuse anything larger. Linux achieves a similar effect through its
// heuristic-overcommit mode at the kernel level.
fn max_segmalloc() size = {
	if (cached_max_segmalloc != 0) return cached_max_segmalloc;
	cached_max_segmalloc = query_max_segmalloc();
	return cached_max_segmalloc;
};

fn query_max_segmalloc() size = {
	// CTL_HW=6, HW_MEMSIZE=24 (sys/sysctl.h)
	let mib_mem: [2]i32 = [6, 24];
	let memsize: u64 = 0;
	let memsize_len: size = size(u64);
	if (sysctl(&mib_mem[0], 2, &memsize: *opaque, &memsize_len,
			null, 0) != 0) {
		// sysctl failed unexpectedly; fall back to a generous default
		// (1 TiB) rather than letting unbounded requests through.
		return 1 << 40;
	};

	let total: size = memsize: size;

	// CTL_VM=2, VM_SWAPUSAGE=5 (sys/sysctl.h)
	let mib_swap: [2]i32 = [2, 5];
	let swap = xsw_usage {
		xsu_total = 0,
		xsu_avail = 0,
		xsu_used = 0,
		xsu_pagesize = 0,
		xsu_encrypted = 0,
	};
	let swap_len: size = size(xsw_usage);
	if (sysctl(&mib_swap[0], 2, &swap: *opaque, &swap_len,
			null, 0) == 0) {
		total += swap.xsu_total: size;
	};

	return total;
};

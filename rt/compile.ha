export type status = enum {
	SUCCESS,
	USER,
	LEX,
	PARSE,
	CHECK,
	_EXEC_FAILED,
	ABNORMAL = 255,
};

fn strstatus(status: int) str = {
	switch (status) {
	case status::SUCCESS =>
		return "success (0)";
	case status::USER =>
		return "user (1)";
	case status::LEX =>
		return "lex (2)";
	case status::PARSE =>
		return "parse (3)";
	case status::CHECK =>
		return "check (4)";
	case status::ABNORMAL =>
		return "abnormal (255)";
	case status::_EXEC_FAILED =>
		return "internal error: compiler execve failed";
	case =>
		return itos(status: int);
	};
};

export type error = !void;

// Runs the Hare compiler and returns the exit status.
export fn compile(
	expected: (status | void),
	src: str,
	flags: str...
) (void | error) = {
	let wstatus = 0;
	let pipefd = [-1, -1];
	assert(pipe2(&pipefd, 0) == 0);

	const child = fork();
	if (child == 0) {
		close(pipefd[1]);
		dup2(pipefd[0], 0);
		close(1);
		close(2);

		// FIXME use $BINOUT variable
		let harec = alloc_cstr("./.bin/harec");
		let argv: []nullable *u8 = alloc([harec]...);

		for (let i = 0z; i < len(flags); i += 1) {
			append(argv, alloc_cstr(flags[i]));
		};
		append(argv, [alloc_cstr("-o/dev/null"), alloc_cstr("-"), null]...);

		execve(harec, *(&argv: **[*]nullable *u8), envp);
		exit(status::_EXEC_FAILED);
	} else {
		assert(child != -1, "fork(2) failed");
		close(pipefd[0]);

		const buf = alloc_cstr(src): *const [*]u8;
		defer free(buf);
		for (let n = 0z; n < len(src)) {
			let m = write(pipefd[1], &buf[n], len(src) - n): size;
			assert(m > 0, "write(2) failed");
			n += m;
		};

		close(pipefd[1]);
		wait4(child, &wstatus, 0, null);
	};

	if (!wifexited(wstatus)) {
		assert(wifsignaled(wstatus));
		write_stderr("signaled ");
		write_stderr(itos(wtermsig(wstatus)));
		write_stderr("\n");
		return error;
	};

	match (expected) {
	case void =>
		const status = wexitstatus(wstatus);
		if (status == status::SUCCESS) {
			write_stderr("expected any failure, got success\n");
			return error;
		};
	case let expected: status =>
		const exit_status = wexitstatus(wstatus);
		if (exit_status == status::_EXEC_FAILED) {
			write_stderr(strstatus(exit_status));
			write_stderr("\n");
			return error;
		};
		if (exit_status != expected) {
			let s = "expected ";
			write_stderr("expected ");
			write_stderr(strstatus(expected));
			write_stderr(", got ");
			write_stderr(strstatus(exit_status));
			write_stderr("\n");
			return error;
		};
	};
};

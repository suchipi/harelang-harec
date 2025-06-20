use rt::{compile, status};

#[this::should::lex()]

#[test::annotation]
#[test::annotation(param, type, "string", 2 + 2)]
#[test::nested(foo(bar[() baz[{}[]]{bat}]))]
export #[annotations] fn #[can] main(#[appear]) #[anywhere] void = {
	compile(status::LEX, "#[(this::should::error)]")!;
	compile(status::LEX, "#[but this should not]")!;
	compile(status::LEX, "#[nor:: ::should::this]")!;
	compile(status::LEX, "# [no::space::allowed]")!;
	compile(status::LEX, "#[mismatched(bracket]]")!;
	compile(status::LEX, "#[mismatched(bracket}]")!;
	compile(status::LEX, "#[mismatched[bracket)]")!;
	compile(status::LEX, "#[mismatched[bracket}]")!;
	compile(status::LEX, "#[mismatched{bracket)]")!;
	compile(status::LEX, "#[mismatched{bracket]]")!;
	compile(status::LEX, "#[mismatched::bracket)")!;
	compile(status::LEX, "#[missing::bracket")!;
};

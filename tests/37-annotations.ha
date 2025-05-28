use rt::{compile, status};

#[test::annotation]
#[test::annotation(param, type, "string", 2 + 2)]
#[test::nested(foo(bar[baz{bat}]))]
export #[annotations] fn #[can] main(#[appear]) #[anywhere] void = {
	compile(status::LEX, "#[(this::should::error)]")!;
	compile(status::CHECK, "#[this::should::lex()]")!;
	compile(status::LEX, "#[but this should not]")!;
	compile(status::LEX, "#[nor:: ::should::this]")!;
};

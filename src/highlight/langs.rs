use crate::highlight::{SadLang, SadLangConf};

pub fn langs(lang: SadLang) -> SadLangConf {
    match lang {
        SadLang::Java => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("//")
            .identifier("class")
            .identifier("static")
            .identifier("private")
            .identifier("public")
            .identifier("void")
            .identifier("null")
            .identifier("extends")
            .identifier("implements")
            .identifier("try")
            .identifier("while")
            .identifier("catch")
            .identifier("finally")
            .identifier("throw")
            .identifier("throws")
            .identifier("interface")
            .identifier("if")
            .identifier("else")
            .identifier("return")
            .identifier("enum")
            .identifier("final")
            .identifier("int")
            .identifier("new"),
        SadLang::Alloy => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("//")
            .identifier("abstract")
            .identifier("all")
            .identifier("and")
            .identifier("as")
            .identifier("assert")
            .identifier("but")
            .identifier("check")
            .identifier("disj")
            .identifier("else")
            .identifier("exactly")
            .identifier("extends")
            .identifier("fact")
            .identifier("for")
            .identifier("fun")
            .identifier("iden")
            .identifier("iff")
            .identifier("implies")
            .identifier("in")
            .identifier("Int")
            .identifier("let")
            .identifier("lone")
            .identifier("for")
            .identifier("fun")
            .identifier("iden")
            .identifier("iff")
            .identifier("implies")
            .identifier("in")
            .identifier("Int")
            .identifier("let")
            .identifier("lone")
            .identifier("module")
            .identifier("no")
            .identifier("none")
            .identifier("not")
            .identifier("one")
            .identifier("open")
            .identifier("or")
            .identifier("pred")
            .identifier("run")
            .identifier("set")
            .identifier("sig")
            .identifier("some")
            .identifier("sum")
            .identifier("univ"),
        SadLang::Erlang => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("//")
            .identifier("when")
            .identifier("case")
            .identifier("of")
            .identifier("end")
            .identifier("pred"),
        SadLang::Elixir => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("#")
            .identifier("def")
            .identifier("defmodule")
            .identifier("defmacro")
            .identifier("defstruct")
            .identifier("quote")
            .identifier("cond")
            .identifier("true")
            .identifier("false")
            .identifier("nil")
            .identifier("do")
            .identifier("end")
            .identifier("import"),
        SadLang::Haskell => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("--")
            .inline_comment("//")
            .identifier("<$>")
            .identifier("=<<")
            .identifier(">>=")
            .identifier("case")
            .identifier("of")
            .identifier("type")
            .identifier("data")
            .identifier("one")
            .identifier("lone")
            .identifier("pred"),
        SadLang::Javascript => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("//")
            .identifier("const")
            .identifier("window")
            .identifier("for")
            .identifier("let")
            .identifier("await")
            .identifier("async")
            .identifier("of")
            .identifier("null")
            .identifier("if")
            .identifier("else"),
        SadLang::Rust => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("//")
            .identifier("struct")
            .identifier("impl")
            .identifier("mut")
            .identifier("self")
            .identifier("return")
            .identifier("fn"),
        // todo: how to make symbols included in the keyword/identifier/etc.
        SadLang::Tla => SadLangConf::init()
            .string('"')
            .comment("/*", "*/")
            .inline_comment("\\*")
            .identifier("\\A")
            .identifier("\\E")
            .identifier("\\in")
            .identifier("\\X")
            .identifier("\\union")
            .identifier("\\div")
            .identifier("\\prec")
            .identifier("\\/")
            .identifier("/\\")
            .identifier("=")
            .identifier("==")
            .identifier("<<")
            .identifier(">>")
            .identifier("{")
            .identifier("}")
            .identifier("~")
            .identifier("EXCEPT")
            .identifier("UNCHANGED")
            .identifier("DOMAIN")
            .identifier("LAMBDA")
            .identifier("SUBSET")
            .identifier("UNION")
            .identifier("CHOOSE")
            .identifier("VARIABLE"),
        SadLang::Text => SadLangConf::init().no_numbers(),
        SadLang::Sql => SadLangConf::init()
            .string("'")
            .identifier("create")
            .identifier("unique")
            .identifier("index")
            .identifier("on")
            .identifier("select")
            .identifier("from")
            .identifier("inner")
            .identifier("join")
            .identifier("insert")
            .identifier("into")
            .identifier("commit")
            .identifier("rollback")
            .identifier("order")
            .identifier("is")
            .identifier("not")
            .identifier("null")
            .identifier("values")
            .identifier("group")
            .identifier("by")
            .identifier("max")
            .identifier("having")
            .identifier("count")
            .identifier("where")
            .identifier("and")
            .identifier("transaction")
            .identifier("begin"),
        SadLang::Bash => SadLangConf::init()
            .string("\"")
            .inline_comment("#")
            .identifier("return")
            .identifier("in")
            .identifier("esac")
            .identifier("if")
            .identifier("fi")
            .identifier("then")
            .identifier("case"),
        SadLang::Entremets => SadLangConf::init()
            .identifier("init")
            .identifier("process")
            .identifier("insert")
            .identifier("into")
            .identifier("values")
            .identifier("select")
            .identifier("from")
            .identifier("where")
            .identifier("update")
            .identifier("set")
            .identifier("property")
            .identifier("eventually")
            .identifier("do")
            .identifier("let")
            .identifier("end"),
    }
}

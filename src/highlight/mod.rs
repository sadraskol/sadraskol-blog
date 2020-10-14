use std::io;

use crate::custom_markdown::StrWrite;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SadLang {
    Java,
    Alloy,
    Erlang,
    Elixir,
    Haskell,
    Javascript,
    Tla,
    Text,
}

type Span = (usize, usize, String);

pub fn highlight<W: StrWrite>(mut w: W, s: &str, l: SadLang) -> io::Result<()> {
    match l {
        SadLang::Tla => {
            let cs = def_lang(
                "tla",
                vec![
                    keyword("\\A"),
                    keyword("\\E"),
                    keyword("\\in"),
                    keyword("EXCEPT"),
                    keyword("UNCHANGED"),
                    keyword("DOMAIN"),
                    keyword("LAMBDA"),
                    inline_comment("\\*"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Java => {
            let cs = def_lang(
                "java",
                vec![
                    keyword("class"),
                    keyword("public"),
                    keyword("static"),
                    keyword("private"),
                    keyword("void"),
                    keyword("null"),
                    keyword("extends"),
                    keyword("implements"),
                    keyword("try"),
                    keyword("while"),
                    keyword("catch"),
                    keyword("finally"),
                    keyword("throw"),
                    keyword("throws"),
                    keyword("interface"),
                    keyword("if"),
                    keyword("else"),
                    keyword("return"),
                    keyword("new"),
                    inline_comment("//"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Alloy => {
            let cs = def_lang(
                "alloy",
                vec![
                    keyword("abstract"),
                    keyword("all"),
                    keyword("and"),
                    keyword("as"),
                    keyword("assert"),
                    keyword("but"),
                    keyword("check"),
                    keyword("disj"),
                    keyword("else"),
                    keyword("exactly"),
                    keyword("extends"),
                    keyword("fact"),
                    keyword("for"),
                    keyword("fun"),
                    keyword("iden"),
                    keyword("iff"),
                    keyword("implies"),
                    keyword("in"),
                    keyword("Int"),
                    keyword("let"),
                    keyword("lone"),
                    keyword("module"),
                    keyword("no"),
                    keyword("none"),
                    keyword("not"),
                    keyword("one"),
                    keyword("open"),
                    keyword("or"),
                    keyword("pred"),
                    keyword("run"),
                    keyword("set"),
                    keyword("sig"),
                    keyword("some"),
                    keyword("sum"),
                    keyword("univ"),
                    inline_comment("//"),
                    inline_comment("--"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Erlang => {
            let cs = def_lang(
                "erlang",
                vec![
                    keyword("when"),
                    keyword("case"),
                    keyword("of"),
                    keyword("end"),
                    keyword("pred"),
                    inline_comment("//"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Elixir => {
            let cs = def_lang(
                "elixir",
                vec![
                    keyword("def"),
                    keyword("defmodule"),
                    keyword("defmacro"),
                    keyword("defstruct"),
                    keyword("quote"),
                    keyword("cond"),
                    keyword("true"),
                    keyword("false"),
                    keyword("nil"),
                    keyword("do"),
                    keyword("end"),
                    keyword("import"),
                    inline_comment("#"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Haskell => {
            let cs = def_lang(
                "haskell",
                vec![
                    keyword("type"),
                    keyword("data"),
                    keyword("one"),
                    keyword("lone"),
                    keyword("pred"),
                    inline_comment("//"),
                    string('"'),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Javascript => {
            let cs = def_lang(
                "javascript",
                vec![
                    keyword("const"),
                    keyword("window"),
                    keyword("for"),
                    keyword("let"),
                    keyword("of"),
                    keyword("null"),
                    keyword("if"),
                    keyword("else"),
                    inline_comment("//"),
                    string('"'),
                    string('\''),
                ],
            );
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Text => w.write_str(s),
    }
}

fn def_lang(lang: &str, tokens: Vec<Tokenizer>) -> Structure {
    Structure {
        start: 0,
        class: lang.to_string(),
        inside_tokens: tokens,
        final_tokens: vec![],
        spans: vec![],
        parent: None,
    }
}

fn keyword(keyword: &str) -> Tokenizer {
    Tokenizer::Waiting {
        params: TokenParams {
            escape_pred: TokenDelimiter::Identifier,
            token: keyword.to_string(),
            class: "keyword".to_string(),
            structure: None,
            include: false,
        },
    }
}

fn inline_comment(start_with: &str) -> Tokenizer {
    Tokenizer::Waiting {
        params: TokenParams {
            escape_pred: TokenDelimiter::Identifier,
            token: start_with.to_string(),
            class: start_with.to_string(),
            structure: Some(Structure {
                start: 0,
                inside_tokens: vec![],
                final_tokens: vec![Tokenizer::Waiting {
                    params: TokenParams {
                        escape_pred: TokenDelimiter::AnyChar,
                        token: "\n".to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                        include: false,
                    },
                }],
                spans: vec![],
                parent: None,
                class: "comment".to_string(),
            }),
            include: false,
        },
    }
}

fn string(separator: char) -> Tokenizer {
    Tokenizer::Waiting {
        params: TokenParams {
            escape_pred: TokenDelimiter::AnyChar,
            token: separator.to_string(),
            class: "string".to_string(),
            structure: Some(Structure {
                start: 0,
                inside_tokens: vec![],
                final_tokens: vec![Tokenizer::Waiting {
                    params: TokenParams {
                        escape_pred: TokenDelimiter::AnyChar,
                        token: separator.to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                        include: true,
                    },
                }],
                spans: vec![],
                parent: None,
                class: "string".to_string(),
            }),
            include: false,
        },
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Structure {
    inside_tokens: Vec<Tokenizer>,
    final_tokens: Vec<Tokenizer>,
    spans: Vec<Span>,
    parent: Option<Box<Structure>>,
    start: usize,
    class: String,
}

impl Structure {
    fn to_parent(&self, eof_size: usize) -> Structure {
        let some_parent = self.parent.clone();
        let mut p = *some_parent.unwrap();

        match self.final_tokens[0].clone() {
            Tokenizer::Waiting { .. } => {
                p.add((self.start, eof_size, self.class.clone()));
            }
            Tokenizer::Matching { .. } => {
                p.add((self.start, eof_size, self.class.clone()));
            }
            Tokenizer::Sleeping { .. } => {
                p.add((self.start, eof_size, self.class.clone()));
            }
            Tokenizer::Candidate { params, start, end } => {
                if params.include {
                    p.add((self.start, end, self.class.clone()));
                } else {
                    p.add((self.start, start, self.class.clone()));
                }
            }
            Tokenizer::Completed { params, start, end } => {
                if params.include {
                    p.add((self.start, end, self.class.clone()));
                } else {
                    p.add((self.start, start, self.class.clone()));
                }
            }
        }
        p
    }
    fn add(&mut self, s: Span) {
        self.spans.push(s);
    }
    fn start(&mut self, start: usize) {
        self.start = start;
    }
    fn eof(&mut self, end: usize) -> Vec<Span> {
        if self.parent.is_some() {
            self.to_parent(end).eof(end)
        } else {
            self.spans.clone()
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum TokenDelimiter {
    AnyChar,
    Identifier,
}

impl TokenDelimiter {
    fn outside_of_token(self, c: char) -> bool {
        match self {
            TokenDelimiter::AnyChar => true,
            TokenDelimiter::Identifier => {
                if c.is_ascii() {
                    match c as u8 {
                        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' => false,
                        _ => true,
                    }
                } else {
                    true
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct TokenParams {
    escape_pred: TokenDelimiter,
    token: String,
    class: String,
    structure: Option<Structure>,
    include: bool,
}

#[derive(Clone, Debug, PartialEq)]
enum Tokenizer {
    Waiting {
        params: TokenParams,
    },
    Matching {
        start: usize,
        valid_acc: Vec<char>,
        missing_acc: Vec<char>,
        params: TokenParams,
    },
    Candidate {
        start: usize,
        end: usize,
        params: TokenParams,
    },
    Completed {
        start: usize,
        end: usize,
        params: TokenParams,
    },
    Sleeping {
        params: TokenParams,
    },
}

impl Tokenizer {
    fn accumulate(&self, c: char, s: usize) -> Self {
        match self {
            Tokenizer::Waiting { params } => {
                let mut valid_acc = vec![];
                let mut missing_acc: Vec<char> = params.token.chars().collect();
                if missing_acc[0] == c {
                    valid_acc.push(c);
                    missing_acc.remove(0);
                    if missing_acc.is_empty() {
                        Tokenizer::Candidate {
                            start: s,
                            end: s + c.len_utf8(),
                            params: params.clone(),
                        }
                    } else {
                        Tokenizer::Matching {
                            start: s,
                            valid_acc,
                            missing_acc,
                            params: params.clone(),
                        }
                    }
                } else if !params.escape_pred.outside_of_token(c) {
                    Tokenizer::Sleeping {
                        params: params.clone(),
                    }
                } else {
                    Tokenizer::Waiting {
                        params: params.clone(),
                    }
                }
            }
            Tokenizer::Matching {
                params,
                start,
                valid_acc,
                missing_acc,
            } => {
                if missing_acc[0] == c {
                    let mut valids = valid_acc.clone();
                    let mut missings = missing_acc.clone();
                    valids.push(c);
                    missings.remove(0);
                    if missings.is_empty() {
                        if params.escape_pred == TokenDelimiter::AnyChar {
                            // TODO This is a special case for structure finalizing token (should be a special case indeed!)
                            Tokenizer::Waiting {
                                params: params.clone(),
                            }
                        } else {
                            Tokenizer::Candidate {
                                start: *start,
                                end: s + c.len_utf8(),
                                params: params.clone(),
                            }
                        }
                    } else {
                        Tokenizer::Matching {
                            missing_acc: missings,
                            valid_acc: valids,
                            start: *start,
                            params: params.clone(),
                        }
                    }
                } else if !params.escape_pred.outside_of_token(c) {
                    Tokenizer::Sleeping {
                        params: params.clone(),
                    }
                } else {
                    Tokenizer::Waiting {
                        params: params.clone(),
                    }
                }
            }
            Tokenizer::Candidate { params, start, end } => {
                if params.escape_pred.outside_of_token(c) {
                    Tokenizer::Completed {
                        start: *start,
                        end: *end,
                        params: params.clone(),
                    }
                } else {
                    Tokenizer::Sleeping {
                        params: params.clone(),
                    }
                }
            }
            Tokenizer::Sleeping { params } => {
                if params.escape_pred.outside_of_token(c) {
                    Tokenizer::Waiting {
                        params: params.clone(),
                    }
                } else {
                    self.clone()
                }
            }
            Tokenizer::Completed { .. } => self.clone(),
        }
    }

    fn is_complete(&self) -> bool {
        match self {
            Tokenizer::Waiting { .. } => false,
            Tokenizer::Sleeping { .. } => false,
            Tokenizer::Matching { .. } => false,
            Tokenizer::Candidate { .. } => false,
            Tokenizer::Completed { .. } => true,
        }
    }

    fn as_span(&self) -> (Self, Span) {
        match self {
            Tokenizer::Waiting { .. } => panic!("Waiting token cannot be converted to span"),
            Tokenizer::Sleeping { .. } => panic!("Sleeping token cannot be converted to span"),
            Tokenizer::Matching { .. } => panic!("Matching token cannot be converted to span"),
            Tokenizer::Candidate { params, start, end } => (
                Tokenizer::Waiting {
                    params: params.clone(),
                },
                (*start, *end, params.class.clone()),
            ),
            Tokenizer::Completed { params, start, end } => (
                Tokenizer::Waiting {
                    params: params.clone(),
                },
                (*start, *end, params.class.clone()),
            ),
        }
    }

    fn structure_starts(&self) -> bool {
        match self {
            Tokenizer::Waiting { params } => params.structure.is_some(),
            Tokenizer::Sleeping { params } => params.structure.is_some(),
            Tokenizer::Matching { params, .. } => params.structure.is_some(),
            Tokenizer::Candidate { params, .. } => params.structure.is_some(),
            Tokenizer::Completed { params, .. } => params.structure.is_some(),
        }
    }

    fn as_struct(&self) -> (Self, Structure) {
        let (params, start) = match self {
            Tokenizer::Waiting { .. } => panic!("Waiting token cannot be converted to structure"),
            Tokenizer::Sleeping { .. } => panic!("Waiting token cannot be converted to structure"),
            Tokenizer::Matching { .. } => panic!("Waiting token cannot be converted to structure"),
            Tokenizer::Candidate { params, start, .. } => (params, start),
            Tokenizer::Completed { params, start, .. } => (params, start),
        };
        let mut structure = params.structure.clone().unwrap();
        structure.start(*start);
        (
            Tokenizer::Waiting {
                params: params.clone(),
            },
            structure,
        )
    }
}

fn highlight_structure<W: StrWrite>(w: &mut W, s: &&str, mut cs: Structure) -> io::Result<()> {
    let mut size = 0;
    for c in s.chars() {
        let mut opt_span = None;
        let mut opt_structure = None;
        cs.inside_tokens = cs
            .inside_tokens
            .iter()
            .map(|t| t.accumulate(c, size))
            .collect();
        cs.final_tokens = cs
            .final_tokens
            .iter()
            .map(|t| t.accumulate(c, size))
            .collect();

        size += c.len_utf8();

        cs.inside_tokens = cs
            .inside_tokens
            .iter()
            .map(|t| {
                if t.is_complete() {
                    if t.structure_starts() {
                        let (s, structure) = t.as_struct();
                        opt_structure = Some(structure);
                        s
                    } else {
                        let (s, span) = t.as_span();
                        opt_span = Some(span);
                        s
                    }
                } else {
                    t.clone()
                }
            })
            .collect();

        if let Some(mut new_cs) = opt_structure {
            new_cs.parent = Some(Box::new(cs));
            cs = new_cs;
        } else if let Some(span) = opt_span {
            cs.add(span);
        }

        if !cs.final_tokens.is_empty() && cs.final_tokens[0].is_complete() {
            cs = cs.to_parent(size);
        }
    }

    let spans: Vec<Span> = cs.eof(size);

    let mut mark = 0;
    for span in spans {
        w.write_str(&s[mark..span.0])?;
        w.write_str(format!("<span class=\"h-{}\">", span.2).as_str())?;
        w.write_str(&s[span.0..span.1])?;
        w.write_str("</span>")?;
        mark = span.1;
    }
    w.write_str(&s[mark..])
}

#[cfg(test)]
mod test {
    use crate::highlight::highlight;
    use crate::highlight::SadLang::{Alloy, Elixir, Java, Text};

    #[test]
    fn text_provided_as_it_is() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "some text code\n", Text).unwrap();
        assert_eq!("some text code\n", s.as_str());
    }

    #[test]
    fn keyword_inserted() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "class text code\n", Java).unwrap();
        assert_eq!(
            "<span class=\"h-keyword\">class</span> text code\n",
            s.as_str()
        );
    }

    #[test]
    fn malformed_java_is_okay() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "some java code\n", Java).unwrap();
        assert_eq!("some java code\n", s.as_str());
    }

    #[test]
    fn inline_comment_is_okay() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "some // java code\n", Java).unwrap();
        assert_eq!(
            "some <span class=\"h-comment\">// java code</span>\n",
            s.as_str()
        );
    }

    #[test]
    fn inline_comment_works_with_eol_delimiter() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "some // java code", Java).unwrap();
        assert_eq!(
            "some <span class=\"h-comment\">// java code</span>",
            s.as_str()
        );
    }

    #[test]
    fn it_works_with_accents_as_well() {
        let mut s = String::with_capacity(100);
        highlight(
            &mut s,
            "verified: set User, // Le service aura un set d'utilisateurs vérifiés\n",
            Alloy,
        )
        .unwrap();
        assert_eq!("verified: <span class=\"h-keyword\">set</span> User, <span class=\"h-comment\">// Le service aura un set d'utilisateurs vérifiés</span>\n", s.as_str());
    }

    #[test]
    fn keywords_are_not_highlighted_if_in_the_end_of_names() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "innerclass", Java).unwrap();
        assert_eq!("innerclass", s.as_str());
    }

    #[test]
    fn keywords_are_not_highlighted_if_starting_of_names() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "classical", Java).unwrap();
        assert_eq!("classical", s.as_str());
    }

    #[test]
    fn highligh_strings() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "\"classical\" wow", Java).unwrap();
        assert_eq!(
            "<span class=\"h-string\">\"classical\"</span> wow",
            s.as_str()
        );
    }

    #[test]
    fn highligh_strings_within_the_rest_elixir() {
        let mut s = String::with_capacity(100);
        highlight(
            &mut s,
            "      def unquote(:\"add_#{name}\")(addend), do: unquote(base_addend) + addend",
            Elixir,
        )
        .unwrap();
        assert_eq!("      <span class=\"h-keyword\">def</span> unquote(:<span class=\"h-string\">\"add_#{name}\"</span>)(addend), <span class=\"h-keyword\">do</span>: unquote(base_addend) + addend", s.as_str());
    }
}

use std::io;

use crate::custom_markdown::StrWrite;

pub mod java;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SadLang {
    Java,
    Alloy,
    Erlang,
    Elixir,
    Haskell,
    Javascript,
    Text,
}

type Span = (usize, usize, String);

pub fn highlight<W: StrWrite>(mut w: W, s: &str, l: SadLang) -> io::Result<()> {
    return match l {
        SadLang::Java => {
            let cs = def_lang("java", vec![
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
                keyword("if"),
                keyword("else"),
                keyword("return"),
                keyword("new"),
                inline_comment("//"),
                string('"'),
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Alloy => {
            let cs = def_lang("alloy", vec![
                keyword("abstract"), keyword("all"), keyword("and"), keyword("as"), keyword("assert"),
                keyword("but"), keyword("check"), keyword("disj"), keyword("else"), keyword("exactly"),
                keyword("extends"), keyword("fact"), keyword("for"), keyword("fun"), keyword("iden"),
                keyword("iff"), keyword("implies"), keyword("in"), keyword("Int"), keyword("let"),
                keyword("lone"), keyword("module"), keyword("no"), keyword("none"), keyword("not"),
                keyword("one"), keyword("open"), keyword("or"), keyword("pred"), keyword("run"),
                keyword("set"), keyword("sig"), keyword("some"), keyword("sum"), keyword("univ"),
                inline_comment("//"), inline_comment("--"),
                string('"'),
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Erlang => {
            let cs = def_lang("erlang", vec![
                keyword("when"),
                keyword("case"),
                keyword("of"),
                keyword("end"),
                keyword("pred"),
                inline_comment("//"),
                string('"'),
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Elixir => {
            let cs = def_lang("elixir", vec![
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
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Haskell => {
            let cs = def_lang("haskell", vec![
                keyword("type"),
                keyword("data"),
                keyword("one"),
                keyword("lone"),
                keyword("pred"),
                inline_comment("//"),
                string('"'),
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Javascript => {
            let cs = def_lang("javascript", vec![
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
            ]);
            highlight_structure(&mut w, &s, cs)
        }
        SadLang::Text => w.write_str(s)
    };
}

fn def_lang(lang: &str, tokens: Vec<STokenizer>) -> Structure {
    return Structure {
        start: 0,
        class: lang.to_string(),
        inside_tokens: tokens,
        final_tokens: vec![],
        spans: vec![],
        parent: None,
    };
}

fn keyword(keyword: &str) -> STokenizer {
    return STokenizer::WaitingToken {
        params: TokenParams {
            escape_chars: vec!['\n', ' '],
            token: keyword.to_string(),
            class: "keyword".to_string(),
            structure: None,
            include: false,
        }
    };
}

fn inline_comment(start_with: &str) -> STokenizer {
    return STokenizer::WaitingToken {
        params: TokenParams {
            escape_chars: vec!['\n', ' '],
            token: start_with.to_string(),
            class: start_with.to_string(),
            structure: Some(Structure {
                start: 0,
                inside_tokens: vec![],
                final_tokens: vec![STokenizer::WaitingToken {
                    params: TokenParams {
                        escape_chars: vec![],
                        token: "\n".to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                        include: false,
                    }
                }],
                spans: vec![],
                parent: None,
                class: "inline-comment".to_string(),
            }),
            include: false,
        }
    };
}

fn string(separator: char) -> STokenizer {
    return STokenizer::WaitingToken {
        params: TokenParams {
            escape_chars: vec![],
            token: separator.to_string(),
            class: "string".to_string(),
            structure: Some(Structure {
                start: 0,
                inside_tokens: vec![],
                final_tokens: vec![STokenizer::WaitingToken {
                    params: TokenParams {
                        escape_chars: vec![],
                        token: separator.to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                        include: true,
                    }
                }],
                spans: vec![],
                parent: None,
                class: "string".to_string(),
            }),
            include: false,
        }
    };
}

#[derive(Clone, Debug, PartialEq)]
struct Structure {
    inside_tokens: Vec<STokenizer>,
    final_tokens: Vec<STokenizer>,
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
            STokenizer::WaitingToken { .. } => { p.add((self.start, eof_size, self.class.clone())); }
            STokenizer::MatchingToken { .. } => { p.add((self.start, eof_size, self.class.clone())); }
            STokenizer::SleepingToken { .. } => { p.add((self.start, eof_size, self.class.clone())); }
            STokenizer::CandidateToken { params, start, end } => {
                if params.include {
                    p.add((self.start, end, self.class.clone()));
                } else {
                    p.add((self.start, start, self.class.clone()));
                }
            }
            STokenizer::CompletedToken { params, start, end } => {
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

#[derive(Clone, Debug, PartialEq)]
struct TokenParams {
    escape_chars: Vec<char>,
    token: String,
    class: String,
    structure: Option<Structure>,
    include: bool,
}

#[derive(Clone, Debug, PartialEq)]
enum STokenizer {
    WaitingToken {
        params: TokenParams
    },
    MatchingToken {
        start: usize,
        valid_acc: Vec<char>,
        missing_acc: Vec<char>,
        params: TokenParams,
    },
    CandidateToken {
        start: usize,
        end: usize,
        params: TokenParams,
    },
    CompletedToken {
        start: usize,
        end: usize,
        params: TokenParams,
    },
    SleepingToken {
        params: TokenParams
    },
}

impl STokenizer {
    fn accumulate(&self, c: char, s: usize) -> Self {
        match self {
            STokenizer::WaitingToken { params } => {
                let mut valid_acc = vec![];
                let mut missing_acc: Vec<char> = params.token.chars().collect();
                if missing_acc[0] == c {
                    valid_acc.push(c);
                    missing_acc.remove(0);
                    if missing_acc.is_empty() {
                        STokenizer::CandidateToken {
                            start: s,
                            end: s + c.len_utf8(),
                            params: params.clone(),
                        }
                    } else {
                        STokenizer::MatchingToken {
                            start: s,
                            valid_acc,
                            missing_acc,
                            params: params.clone(),
                        }
                    }
                } else if !params.escape_chars.is_empty() && !params.escape_chars.contains(&c) {
                    STokenizer::SleepingToken {
                        params: params.clone(),
                    }
                } else {
                    STokenizer::WaitingToken {
                        params: params.clone()
                    }
                }
            }
            STokenizer::MatchingToken { params, start, valid_acc, missing_acc } => {
                if missing_acc[0] == c {
                    let mut valids = valid_acc.clone();
                    let mut missings = missing_acc.clone();
                    valids.push(c);
                    missings.remove(0);
                    if missings.is_empty() {
                        if params.escape_chars.is_empty() {
                            // TODO This is a special case for structure finalizing token (should be a special case indeed!)
                            STokenizer::WaitingToken {
                                params: params.clone(),
                            }
                        } else {
                            STokenizer::CandidateToken {
                                start: *start,
                                end: s + c.len_utf8(),
                                params: params.clone(),
                            }
                        }
                    } else {
                        STokenizer::MatchingToken {
                            missing_acc: missings,
                            valid_acc: valids,
                            start: *start,
                            params: params.clone(),
                        }
                    }
                } else {
                    if !params.escape_chars.is_empty() && !params.escape_chars.contains(&c) {
                        STokenizer::SleepingToken {
                            params: params.clone(),
                        }
                    } else {
                        STokenizer::WaitingToken {
                            params: params.clone(),
                        }
                    }
                }
            }
            STokenizer::CandidateToken { params, start, end } => {
                if params.escape_chars.is_empty() || params.escape_chars.contains(&c) {
                    STokenizer::CompletedToken {
                        start: *start,
                        end: *end,
                        params: params.clone(),
                    }
                } else {
                    STokenizer::SleepingToken {
                        params: params.clone()
                    }
                }
            }
            STokenizer::SleepingToken { params } => {
                if params.escape_chars.is_empty() || params.escape_chars.contains(&c) {
                    STokenizer::WaitingToken {
                        params: params.clone()
                    }
                } else {
                    self.clone()
                }
            }
            STokenizer::CompletedToken { .. } => { self.clone() }
        }
    }
    fn is_complete(&self) -> bool {
        match self {
            STokenizer::WaitingToken { .. } => false,
            STokenizer::SleepingToken { .. } => false,
            STokenizer::MatchingToken { .. } => false,
            STokenizer::CandidateToken { .. } => false,
            STokenizer::CompletedToken { .. } => true,
        }
    }
    fn as_span(&self) -> (Self, Span) {
        match self {
            STokenizer::WaitingToken { .. } => panic!("Waiting token cannot be converted to span"),
            STokenizer::SleepingToken { .. } => panic!("Sleeping token cannot be converted to span"),
            STokenizer::MatchingToken { .. } => panic!("Matching token cannot be converted to span"),
            STokenizer::CandidateToken { params, start, end } => {
                (
                    STokenizer::WaitingToken { params: params.clone() },
                    (*start, *end, params.class.clone())
                )
            }
            STokenizer::CompletedToken { params, start, end } => {
                (
                    STokenizer::WaitingToken { params: params.clone() },
                    (*start, *end, params.class.clone())
                )
            }
        }
    }
    fn structure_starts(&self) -> bool {
        match self {
            STokenizer::WaitingToken { params } => { params.structure.is_some() }
            STokenizer::SleepingToken { params } => { params.structure.is_some() }
            STokenizer::MatchingToken { params, .. } => { params.structure.is_some() }
            STokenizer::CandidateToken { params, .. } => { params.structure.is_some() }
            STokenizer::CompletedToken { params, .. } => { params.structure.is_some() }
        }
    }
    fn as_struct(&self) -> (Self, Structure) {
        let (params, start) = match self {
            STokenizer::WaitingToken { .. } => panic!("Waiting token cannot be converted to structure"),
            STokenizer::SleepingToken { .. } => panic!("Waiting token cannot be converted to structure"),
            STokenizer::MatchingToken { .. } => panic!("Waiting token cannot be converted to structure"),
            STokenizer::CandidateToken { params, start, .. } => { (params, start) }
            STokenizer::CompletedToken { params, start, .. } => { (params, start) }
        };
        let mut structure = params.structure.clone().unwrap();
        structure.start(*start);
        (STokenizer::WaitingToken { params: params.clone() }, structure)
    }
}

fn highlight_structure<W: StrWrite>(w: &mut W, s: &&str, mut cs: Structure) -> io::Result<()> {
    let mut size = 0;
    for c in s.chars() {
        let mut opt_span = None;
        let mut opt_structure = None;
        cs.inside_tokens = cs.inside_tokens.iter()
            .map(|t| {
                t.accumulate(c, size)
            })
            .collect();
        cs.final_tokens = cs.final_tokens.iter()
            .map(|t| {
                t.accumulate(c, size)
            })
            .collect();

        size += c.len_utf8();

        cs.inside_tokens = cs.inside_tokens.iter()
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

        if opt_structure.is_some() {
            let mut new_cs = opt_structure.unwrap();
            new_cs.parent = Some(Box::new(cs));
            cs = new_cs;
        } else if opt_span.is_some() {
            cs.add(opt_span.unwrap());
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
        assert_eq!("<span class=\"h-keyword\">class</span> text code\n", s.as_str());
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
        assert_eq!("some <span class=\"h-inline-comment\">// java code</span>\n", s.as_str());
    }

    #[test]
    fn inline_comment_works_with_eol_delimiter() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "some // java code", Java).unwrap();
        assert_eq!("some <span class=\"h-inline-comment\">// java code</span>", s.as_str());
    }

    #[test]
    fn it_works_with_accents_as_well() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "verified: set User, // Le service aura un set d'utilisateurs vérifiés\n", Alloy).unwrap();
        assert_eq!("verified: <span class=\"h-keyword\">set</span> User, <span class=\"h-inline-comment\">// Le service aura un set d'utilisateurs vérifiés</span>\n", s.as_str());
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
        assert_eq!("<span class=\"h-string\">\"classical\"</span> wow", s.as_str());
    }

    #[test]
    fn highligh_strings_within_the_rest_elixir() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "      def unquote(:\"add_#{name}\")(addend), do: unquote(base_addend) + addend", Elixir).unwrap();
        assert_eq!("      <span class=\"h-keyword\">def</span> unquote(:<span class=\"h-string\">\"add_#{name}\"</span>)(addend), do: unquote(base_addend) + addend", s.as_str());
    }
}
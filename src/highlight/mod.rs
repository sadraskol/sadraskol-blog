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

fn def_lang(lang: &str, tokens: Vec<Tokenizer>) -> Structure {
    return Structure {
        start: 0,
        class: lang.to_string(),
        inside_tokens: tokens,
        final_tokens: vec![],
        spans: vec![],
        parent: None,
    };
}

fn keyword(keyword: &str) -> Tokenizer {
    return Tokenizer {
        start: 0,
        end: 0,
        state: TokenizerState::Waiting,
        escape_chars: vec!['\n', ' '],
        valid_acc: vec![],
        missing_acc: keyword.chars().collect(),
        token: keyword.to_string(),
        class: "keyword".to_string(),
        structure: None,
        include: false,
    };
}

fn inline_comment(start_with: &str) -> Tokenizer {
    return Tokenizer {
        start: 0,
        end: 0,
        state: TokenizerState::Waiting,
        valid_acc: vec![],
        escape_chars: vec!['\n', ' '],
        missing_acc: start_with.chars().collect(),
        token: start_with.to_string(),
        class: "comment".to_string(),
        include: false,
        structure: Some(Structure {
            start: 0,
            inside_tokens: vec![],
            final_tokens: vec![Tokenizer {
                start: 0,
                end: 0,
                escape_chars: vec![],
                state: TokenizerState::Waiting,
                valid_acc: vec![],
                missing_acc: vec!['\n'],
                token: "\n".to_string(),
                class: "end-comment".to_string(),
                structure: None,
                include: false,
            }],
            spans: vec![],
            parent: None,
            class: "inline-comment".to_string(),
        }),
    };
}

fn string(separator: char) -> Tokenizer {
    return Tokenizer {
        start: 0,
        end: 0,
        state: TokenizerState::Waiting,
        valid_acc: vec![],
        escape_chars: vec![],
        missing_acc: vec![separator],
        token: separator.to_string(),
        class: "string".to_string(),
        include: false,
        structure: Some(Structure {
            start: 0,
            inside_tokens: vec![],
            final_tokens: vec![Tokenizer {
                start: 0,
                end: 0,
                state: TokenizerState::Waiting,
                valid_acc: vec![],
                escape_chars: vec![],
                missing_acc: vec![separator],
                token: separator.to_string(),
                class: "end-comment".to_string(),
                structure: None,
                include: true,
            }],
            spans: vec![],
            parent: None,
            class: "string".to_string(),
        }),
    };
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
    fn every_token<F>(&mut self, f: F)
        where F: FnMut(&mut Tokenizer)
    {
        self.inside_tokens.iter_mut()
            .chain(self.final_tokens.iter_mut())
            .for_each(f)
    }
    fn to_parent(&self, end: usize) -> Structure {
        let some_parent = self.parent.clone();
        let mut p = *some_parent.unwrap();

        if self.final_tokens[0].is_at_least_candidate() {
            if self.final_tokens[0].include {
                p.add((self.start, self.final_tokens[0].end, self.class.clone()));
            } else {
                p.add((self.start, self.final_tokens[0].start, self.class.clone()));
            }
        } else {
            p.add((self.start, end, self.class.clone()));
        }

        p
    }
    fn is_complete(&self) -> bool {
        self.final_tokens.iter().any(|t| t.is_complete())
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
enum TokenizerState {
    Waiting,
    Matching,
    Candidate,
    Completed,
    Sleeping,
}

#[derive(Clone, Debug, PartialEq)]
struct Tokenizer {
    start: usize,
    end: usize,
    state: TokenizerState,
    escape_chars: Vec<char>,
    // TODO replace with Predicate
    valid_acc: Vec<char>,
    missing_acc: Vec<char>,
    token: String,
    class: String,
    structure: Option<Structure>,
    include: bool,
}

impl Tokenizer {
    fn accumulate(&mut self, c: char, s: usize) {
        match self.state {
            TokenizerState::Waiting => {
                if self.missing_acc[0] == c {
                    if self.valid_acc.is_empty() {
                        self.start = s;
                    }
                    self.valid_acc.push(c);
                    self.missing_acc.remove(0);
                    if self.missing_acc.is_empty() {
                        self.end = s + c.len_utf8();
                        self.state = TokenizerState::Candidate;
                    } else {
                        self.state = TokenizerState::Matching;
                    }
                } else if !self.escape_chars.is_empty() && !self.escape_chars.contains(&c) {
                    self.state = TokenizerState::Sleeping;
                }
            }
            TokenizerState::Candidate => {
                if self.escape_chars.is_empty() || self.escape_chars.contains(&c) {
                    self.state = TokenizerState::Completed;
                } else {
                    self.state = TokenizerState::Sleeping;
                }
            }
            TokenizerState::Completed => {}
            TokenizerState::Matching => {
                if self.missing_acc[0] == c {
                    if self.valid_acc.is_empty() {
                        self.start = s;
                    }
                    self.valid_acc.push(c);
                    self.missing_acc.remove(0);
                    if self.missing_acc.is_empty() {
                        self.end = s + c.len_utf8();
                        if self.escape_chars.is_empty() {
                            self.valid_acc = vec![];
                            self.missing_acc = self.token.chars().collect();
                            self.state = TokenizerState::Waiting;
                        } else {
                            self.state = TokenizerState::Candidate;
                        }
                    } else {
                        self.state = TokenizerState::Matching;
                    }
                } else {
                    self.valid_acc = vec![];
                    self.missing_acc = self.token.chars().collect();
                    if !self.escape_chars.is_empty() && !self.escape_chars.contains(&c) {
                        self.state = TokenizerState::Sleeping;
                    } else {
                        self.state = TokenizerState::Waiting;
                    }
                }
            }
            TokenizerState::Sleeping => {
                if self.escape_chars.is_empty() || self.escape_chars.contains(&c) {
                    self.valid_acc = vec![];
                    self.missing_acc = self.token.chars().collect();
                    self.state = TokenizerState::Waiting;
                }
            }
        }
    }
    fn is_complete(&self) -> bool {
        self.state == TokenizerState::Completed
    }
    fn is_at_least_candidate(&self) -> bool {
        self.state == TokenizerState::Completed || self.state == TokenizerState::Candidate
    }
    fn as_span(&mut self) -> Span {
        self.valid_acc = vec![];
        self.missing_acc = self.token.chars().collect();
        self.state = TokenizerState::Waiting;
        (self.start, self.end, self.class.clone())
    }
    fn structure_starts(&self) -> bool {
        self.structure.is_some()
    }
    fn as_struct(&mut self) -> Structure {
        self.valid_acc = vec![];
        self.missing_acc = self.token.chars().collect();
        self.state = TokenizerState::Waiting;
        let mut structure = self.structure.clone().unwrap();
        structure.start(self.start);
        structure
    }
}

fn highlight_structure<W: StrWrite>(w: &mut W, s: &&str, mut cs: Structure) -> io::Result<()> {
    let mut size = 0;
    for c in s.chars() {
        let mut opt_span = None;
        let mut opt_structure = None;
        cs.inside_tokens.iter_mut()
            .chain(cs.final_tokens.iter_mut())
            .for_each(|t| {
                t.accumulate(c, size);
            });

        size += c.len_utf8();

        cs.inside_tokens.iter_mut()
            .for_each(|t| {
                if t.is_complete() {
                    if t.structure_starts() {
                        opt_structure = Some(t.as_struct());
                    } else {
                        opt_span = Some(t.as_span());
                    }
                }
            });

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
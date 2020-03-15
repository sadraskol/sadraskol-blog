use std::io;

use crate::custom_markdown::StrWrite;

pub mod java;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SadLang {
    Java,
    Alloy,
    Text,
}

type Span = (usize, usize, String);

pub fn highlight<W: StrWrite>(mut w: W, s: &str, l: SadLang) -> io::Result<()> {
    return match l {
        SadLang::Java => highlight_java(&mut w, &s),
        SadLang::Alloy => highlight_alloy(&mut w, &s),
        SadLang::Text => w.write_str(s)
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
        if self.final_tokens[0].start == 0 {
            p.add((self.start, end, self.class.clone()));
        } else {
            p.add((self.start, self.final_tokens[0].start, self.class.clone()));
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

#[derive(Clone, Debug, PartialEq)]
struct Tokenizer {
    start: usize,
    valid_acc: Vec<char>,
    missing_acc: Vec<char>,
    token: String,
    class: String,
    structure: Option<Structure>,
}

impl Tokenizer {
    fn accumulate(&mut self, c: char, s: usize) {
        if self.missing_acc[0] == c {
            if self.valid_acc.is_empty() {
                self.start = s;
            }
            self.valid_acc.push(c);
            self.missing_acc.remove(0);
        } else {
            self.valid_acc = vec![];
            self.missing_acc = self.token.chars().collect();
        }
    }
    fn is_complete(&self) -> bool {
        self.missing_acc.is_empty()
    }
    fn as_span(&mut self, end: usize) -> Span {
        self.valid_acc = vec![];
        self.missing_acc = self.token.chars().collect();
        (self.start, end, self.class.clone())
    }
    fn structure_starts(&self) -> bool {
        self.structure.is_some()
    }
    fn as_struct(&mut self) -> Structure {
        let mut structure = self.structure.clone().unwrap();
        structure.start(self.start);
        structure
    }
}

fn highlight_java<W: StrWrite>(w: &mut W, s: &&str) -> io::Result<()> {
    let mut cs = Structure {
        start: 0,
        class: "java".to_string(),
        inside_tokens: vec![
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "class".chars().collect(),
                token: "class".to_string(),
                class: "keyword".to_string(),
                structure: None,
            },
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "//".chars().collect(),
                token: "//".to_string(),
                class: "comment".to_string(),
                structure: Some(Structure {
                    start: 0,
                    inside_tokens: vec![],
                    final_tokens: vec![Tokenizer {
                        start: 0,
                        valid_acc: vec![],
                        missing_acc: vec!['\n'],
                        token: "\n".to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                    }],
                    spans: vec![],
                    parent: None,
                    class: "inline-comment".to_string(),
                }),
            }
        ],
        final_tokens: vec![],
        spans: vec![],
        parent: None,
    };
    let mut size = 0;
    for c in s.chars() {
        let mut opt_span = None;
        let mut opt_structure = None;
        cs.every_token(|t| {
            t.accumulate(c, size);
        });

        size += c.len_utf8();

        cs.every_token(|t| {
            if t.is_complete() {
                if t.structure_starts() {
                    opt_structure = Some(t.as_struct());
                } else {
                    opt_span = Some(t.as_span(size));
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
        if cs.is_complete() {
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

fn highlight_alloy<W: StrWrite>(w: &mut W, s: &&str) -> io::Result<()> {
    let mut cs = Structure {
        start: 0,
        class: "alloy".to_string(),
        inside_tokens: vec![
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "sig".chars().collect(),
                token: "sig".to_string(),
                class: "keyword".to_string(),
                structure: None,
            },
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "one".chars().collect(),
                token: "one".to_string(),
                class: "keyword".to_string(),
                structure: None,
            },
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "lone".chars().collect(),
                token: "lone".to_string(),
                class: "keyword".to_string(),
                structure: None,
            },
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "pred".chars().collect(),
                token: "pred".to_string(),
                class: "keyword".to_string(),
                structure: None,
            },
            Tokenizer {
                start: 0,
                valid_acc: vec![],
                missing_acc: "//".chars().collect(),
                token: "//".to_string(),
                class: "comment".to_string(),
                structure: Some(Structure {
                    start: 0,
                    inside_tokens: vec![],
                    final_tokens: vec![Tokenizer {
                        start: 0,
                        valid_acc: vec![],
                        missing_acc: vec!['\n'],
                        token: "\n".to_string(),
                        class: "end-comment".to_string(),
                        structure: None,
                    }],
                    spans: vec![],
                    parent: None,
                    class: "inline-comment".to_string(),
                }),
            }
        ],
        final_tokens: vec![],
        spans: vec![],
        parent: None,
    };
    let mut size = 0;
    for c in s.chars() {
        let mut opt_span = None;
        let mut opt_structure = None;
        cs.every_token(|t| {
            t.accumulate(c, size);
        });

        size += c.len_utf8();

        cs.every_token(|t| {
            if t.is_complete() {
                if t.structure_starts() {
                    opt_structure = Some(t.as_struct());
                } else {
                    opt_span = Some(t.as_span(size));
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
        if cs.is_complete() {
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
    use crate::highlight::SadLang::{Alloy, Java, Text};

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
    fn it_should_work_with_accents_as_well() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "verified: set User, // Le service aura un set d'utilisateurs vérifiés\n", Alloy).unwrap();
        assert_eq!("verified: set User, <span class=\"h-inline-comment\">// Le service aura un set d'utilisateurs vérifiés</span>\n", s.as_str());
    }
}
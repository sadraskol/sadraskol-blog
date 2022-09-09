mod langs;

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
    Rust,
    Tla,
    Text,
    Sql,
    Bash,
}

pub fn highlight<W: StrWrite>(mut w: W, s: &str, l: SadLang) -> io::Result<()> {
    highlight_lang(&mut w, &s, l)
}

pub struct SadLangConf {
    string: String,
    comment: (String, String),
    inline_comment: Vec<String>,
    identifiers: Vec<String>,
    numbers: bool,
}

impl SadLangConf {
    pub fn init() -> Self {
        SadLangConf {
            string: "".to_string(),
            comment: ("su".to_string(), "le".to_string()),
            inline_comment: vec![],
            identifiers: vec![],
            numbers: true,
        }
    }

    pub fn no_numbers(mut self) -> Self {
        self.numbers = false;
        self
    }

    pub fn string<S: ToString>(mut self, s: S) -> Self {
        self.string = s.to_string();
        self
    }

    pub fn comment<S: ToString>(mut self, s: S, e: S) -> Self {
        self.comment = (s.to_string(), e.to_string());
        self
    }

    pub fn inline_comment<S: ToString>(mut self, s: S) -> Self {
        self.inline_comment.push(s.to_string());
        self
    }

    pub fn identifier<S: ToString>(mut self, iden: S) -> Self {
        self.identifiers.push(iden.to_string());
        self
    }
}

struct Parser<'a> {
    source: &'a str,
    start: usize,
    current: usize,
    lang: SadLangConf,
}

#[derive(Debug)]
enum TokenType {
    Eof,
    Transparent,
    Identifier,
    String,
    Number,
    Comment,
    InlineComment,
}

#[derive(Debug)]
struct Token {
    kind: TokenType,
    lexeme: String,
}

impl<'a> Parser<'a> {
    fn init(source: &'a str, lang: SadLangConf) -> Self {
        Parser {
            source,
            start: 0,
            current: 0,
            lang,
        }
    }

    pub fn scan_token(&mut self) -> Token {
        self.start = self.current;
        if self.is_at_end() {
            self.make_token(TokenType::Eof)
        } else {
            let c = self.advance();

            if self.is_identifier_start(c) {
                return self.identifier();
            }
            if self.lang.numbers && c.is_numeric() {
                return self.number();
            }

            if self.is_string_start(c) {
                return self.string();
            }

            if self.has_inline_comment_start(c) {
                return self.inline_comment();
            }

            if self.is_comment_start(c) {
                return self.comment();
            }

            self.make_token(TokenType::Transparent)
        }
    }

    fn identifier(&mut self) -> Token {
        let mut n = 0;
        let mut candidates: Vec<_> = self
            .lang
            .identifiers
            .clone()
            .iter()
            .cloned()
            .filter(|ident| ident.chars().next().unwrap() == self.previous())
            .collect();
        while !self.is_at_end() && (self.peek() == '_' || self.peek().is_alphanumeric()) {
            self.advance();
            n += 1;

            candidates = candidates
                .iter()
                .cloned()
                .filter(|ident| ident.chars().nth(n) == Some(self.previous()))
                .collect();
        }

        let matching = candidates
            .iter()
            .cloned()
            .find(|s| s == &self.current_lexeme());

        if matching.is_none() {
            self.make_token(TokenType::Transparent)
        } else {
            self.make_token(TokenType::Identifier)
        }
    }

    fn is_identifier_start(&self, c: char) -> bool {
        c == '_' || c.is_alphabetic()
    }

    fn string(&mut self) -> Token {
        while !self.is_string_end() && !self.is_at_end() {
            self.advance();
        }

        if self.is_at_end() {
            self.make_token(TokenType::Transparent)
        } else {
            self.string_end();
            self.make_token(TokenType::String)
        }
    }

    fn is_string_start(&self, c: char) -> bool {
        let mut chars = self.lang.string.chars();
        if chars.next() != Some(c) {
            return false;
        }
        for (n, c) in chars.enumerate() {
            if self.peek_nth(n) != Some(c) {
                return false;
            }
        }
        true
    }

    fn is_string_end(&self) -> bool {
        for (n, c) in self.lang.string.chars().enumerate() {
            if self.peek_nth(n) != Some(c) {
                return false;
            }
        }
        true
    }

    fn string_end(&mut self) {
        for _ in (self.lang.string).clone().chars() {
            self.advance();
        }
    }

    fn comment(&mut self) -> Token {
        while !self.is_comment_end() && !self.is_at_end() {
            self.advance();
        }

        if self.is_at_end() {
            self.make_token(TokenType::Transparent)
        } else {
            self.comment_end();
            self.make_token(TokenType::Comment)
        }
    }

    fn is_comment_start(&self, c: char) -> bool {
        let mut chars = self.lang.comment.0.chars();
        if chars.next() != Some(c) {
            return false;
        }
        for (n, c) in chars.enumerate() {
            if self.peek_nth(n) != Some(c) {
                return false;
            }
        }
        true
    }

    fn is_comment_end(&self) -> bool {
        for (n, c) in self.lang.comment.1.chars().enumerate() {
            if self.peek_nth(n) != Some(c) {
                return false;
            }
        }
        true
    }

    fn comment_end(&mut self) {
        for _ in (self.lang.comment.1).clone().chars() {
            self.advance();
        }
    }

    fn inline_comment(&mut self) -> Token {
        while !self.is_at_end() && self.peek() != '\n' {
            self.advance();
        }

        self.make_token(TokenType::InlineComment)
    }

    fn has_inline_comment_start(&self, c: char) -> bool {
        self.lang.inline_comment.iter().any(|start| {
            let mut chars = start.chars();
            if chars.next() != Some(c) {
                return false;
            }
            for (n, c) in chars.enumerate() {
                if self.peek_nth(n) != Some(c) {
                    return false;
                }
            }
            true
        })
    }

    fn number(&mut self) -> Token {
        while !self.is_at_end() && self.peek().is_numeric() {
            self.advance();
        }

        self.make_token(TokenType::Number)
    }

    fn current_lexeme(&self) -> String {
        self.source
            .chars()
            .skip(self.start)
            .take(self.current - self.start)
            .collect()
    }

    fn previous(&self) -> char {
        self.source.chars().nth(self.current - 1).unwrap()
    }

    fn peek(&self) -> char {
        self.source.chars().nth(self.current).unwrap()
    }

    fn peek_nth(&self, n: usize) -> Option<char> {
        self.source.chars().nth(self.current + n)
    }

    fn make_token(&self, kind: TokenType) -> Token {
        Token {
            kind,
            lexeme: self.current_lexeme(),
        }
    }

    fn is_at_end(&self) -> bool {
        self.current == self.source.chars().count()
    }

    fn advance(&mut self) -> char {
        assert!(!self.is_at_end());
        self.current += 1;
        self.source.chars().nth(self.current - 1).unwrap()
    }
}

fn translate(token: Token) -> String {
    match token.kind {
        TokenType::Eof => token.lexeme,
        TokenType::Transparent => token.lexeme,
        TokenType::Identifier => format!("<span class=\"h-keyword\">{}</span>", token.lexeme),
        TokenType::String => format!("<span class=\"h-string\">{}</span>", token.lexeme),
        TokenType::Number => format!("<span class=\"h-number\">{}</span>", token.lexeme),
        TokenType::Comment => format!("<span class=\"h-comment\">{}</span>", token.lexeme),
        TokenType::InlineComment => format!("<span class=\"h-comment\">{}</span>", token.lexeme),
    }
}

fn highlight_lang<W: StrWrite>(w: &mut W, s: &&str, lang: SadLang) -> io::Result<()> {
    let conf = langs::langs(lang);
    let mut parser = Parser::init(s.clone(), conf);
    loop {
        let token = parser.scan_token();

        if matches!(token.kind, TokenType::Eof) {
            break;
        } else {
            w.write_str(&translate(token))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use crate::highlight::highlight;
    use crate::highlight::SadLang::{Alloy, Elixir, Haskell, Java, Sql, Text};

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
    fn highlight_strings() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "\"classical\" wow", Java).unwrap();
        assert_eq!(
            "<span class=\"h-string\">\"classical\"</span> wow",
            s.as_str()
        );
    }

    #[test]
    fn highlight_strings_within_the_rest_elixir() {
        let mut s = String::with_capacity(100);
        highlight(
            &mut s,
            "      def unquote(:\"add_#{name}\")(addend), do: unquote(base_addend) + addend",
            Elixir,
        )
        .unwrap();
        assert_eq!("      <span class=\"h-keyword\">def</span> unquote(:<span class=\"h-string\">\"add_#{name}\"</span>)(addend), <span class=\"h-keyword\">do</span>: unquote(base_addend) + addend", s.as_str());
    }

    #[test]
    fn highlights_numbers() {
        for i in 0..1000 {
            let mut s = String::with_capacity(100);
            highlight(&mut s, &format!("  {}  ", i), Sql).unwrap();
            assert_eq!(
                &format!("  <span class=\"h-number\">{}</span>  ", i),
                s.as_str()
            );
        }
    }

    #[test]
    fn do_not_highlight_number_in_middle_of_an_identifier() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "  t1er  ", Sql).unwrap();
        assert_eq!("  t1er  ", s.as_str());
    }

    #[test]
    fn text_does_not_highlight_numbers() {
        let mut s = String::with_capacity(100);
        highlight(&mut s, "  123  ", Text).unwrap();
        assert_eq!("  123  ", s.as_str());
    }

    #[test]
    fn highlights_multiple_comments() {
        let mut s = String::with_capacity(100);
        highlight(
            &mut s,
            "  -- some comment for this line\nother text  ",
            Haskell,
        )
        .unwrap();
        assert_eq!(
            "  <span class=\"h-comment\">-- some comment for this line</span>\nother text  ",
            s.as_str()
        );
    }
}

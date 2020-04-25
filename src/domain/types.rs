use std::str::FromStr;

use pulldown_cmark::{Options, Parser};

use crate::custom_markdown::sad_push_html;

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PostId(uuid::Uuid);

impl PostId {
    pub fn new(uuid: uuid::Uuid) -> PostId { PostId(uuid) }
    pub fn to_str(&self) -> String {
        self.0.to_hyphenated().to_string()
    }
    pub fn to_uuid(&self) -> uuid::Uuid { self.0.clone() }
}

impl std::fmt::Display for PostId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_str().as_str())
    }
}

impl std::fmt::Debug for PostId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_str().as_str())
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Language { Fr, En }

impl FromStr for Language {
    type Err = ();

    fn from_str(s: &str) -> Result<Language, ()> {
        match s {
            "fr" => Ok(Language::Fr),
            "en" => Ok(Language::En),
            _ => Err(()),
        }
    }
}

impl ToString for Language {
    fn to_string(&self) -> String {
        return match self {
            Language::Fr => "fr".to_string(),
            Language::En => "en".to_string(),
        };
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Markdown {
    raw: String
}

impl Markdown {
    pub fn new<T: ToString>(value: T) -> Markdown {
        Markdown { raw: value.to_string() }
    }

    pub fn format(&self) -> String {
        let mut options = Options::empty();
        options.insert(Options::ENABLE_STRIKETHROUGH);
        options.insert(Options::ENABLE_TABLES);
        let mut parser = Parser::new_ext(self.raw.as_str(), options);

        let mut html_output: String = String::with_capacity(self.raw.len() * 2);
        sad_push_html(&mut html_output, &mut parser);
        html_output.clone()
    }

    pub fn to_edit(&self) -> String {
        self.raw.clone()
    }
}
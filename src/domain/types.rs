use chrono::{DateTime, Utc};
use pulldown_cmark::{Options, Parser};

use crate::custom_markdown::sad_push_html;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Markdown {
    raw: String,
}

impl Markdown {
    pub fn new<T: ToString>(value: T) -> Markdown {
        Markdown {
            raw: value.to_string(),
        }
    }

    pub fn format(&self) -> String {
        let mut options = Options::empty();
        options.insert(Options::ENABLE_STRIKETHROUGH);
        options.insert(Options::ENABLE_TABLES);
        let mut parser = Parser::new_ext(self.raw.as_str(), options);

        let mut html_output: String = String::with_capacity(self.raw.len() * 2);
        sad_push_html(&mut html_output, &mut parser);
        html_output
    }
}

pub struct SadPost {
    pub title: String,
    pub language: String,
    pub publication_date: DateTime<Utc>,
    pub saddown_content: Markdown,
    pub image: Option<String>,
}

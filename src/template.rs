use askama::Template;

use crate::domain::slugify::slugify;
use crate::domain::types::SadPost;

pub struct PostSummaryView {
    title: String,
    publication_date: String,
    language: String,
    view_link: String,
}

impl PostSummaryView {
    pub fn for_human(p: &SadPost) -> Self {
        PostSummaryView {
            title: p.title.clone(),
            language: p.language.to_string(),
            publication_date: p.publication_date.human_format(&p.language),
            view_link: format!("/posts/{}", slugify(&p.title)),
        }
    }

    pub fn for_robot(p: &SadPost) -> Self {
        PostSummaryView {
            title: p.title.clone(),
            language: p.language.to_string(),
            publication_date: p.publication_date.to_rfc3339(),
            view_link: format!("/posts/{}", slugify(&p.title)),
        }
    }
}

#[derive(Template)]
#[template(path = "index.html")]
pub struct IndexTemplate<'a> {
    pub title: &'a str,
    pub posts: Vec<PostSummaryView>,
}

impl<'a> IndexTemplate<'a> {
    pub fn new(posts: Vec<PostSummaryView>) -> Self {
        IndexTemplate {
            title: "Sadraskol",
            posts,
        }
    }
}

#[derive(Template)]
#[template(path = "post.html")]
pub struct PostTemplate<'a> {
    pub title: &'a str,
    pub publication_date: &'a str,
    pub back_link: &'a str,
    pub raw_content: &'a str,
}

#[derive(Template)]
#[template(path = "feed.xml")]
pub struct FeedTemplate {
    pub posts: Vec<PostSummaryView>,
}

impl<'a> AboutTemplate<'a> {
    pub fn new() -> Self {
        AboutTemplate {
            title: "Sadraskol - About Me",
        }
    }
}

#[derive(Template)]
#[template(path = "about.html")]
pub struct AboutTemplate<'a> {
    pub title: &'a str,
}

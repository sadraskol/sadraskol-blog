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
            publication_date: p.publication_date.format("%d %B %Y").to_string(),
            view_link: format!("/posts/{}", slugify(p.title.clone())),
        }
    }

    pub fn for_robot(p: &SadPost) -> Self {
        PostSummaryView {
            title: p.title.clone(),
            language: p.language.to_string(),
            publication_date: p.publication_date.to_rfc3339(),
            view_link: format!("/posts/{}", slugify(p.title.clone())),
        }
    }
}

#[derive(Template)]
#[template(path = "base.html")]
pub struct BaseTemplate<'a> {
    pub title: &'a str,
}

impl<'a> BaseTemplate<'a> {
    pub fn default() -> BaseTemplate<'a> {
        BaseTemplate { title: "Sadraskol" }
    }
}

#[derive(Template)]
#[template(path = "index.html")]
pub struct IndexTemplate<'a> {
    _parent: BaseTemplate<'a>,
    posts: Vec<PostSummaryView>,
}

impl<'a> IndexTemplate<'a> {
    pub fn new(posts: Vec<PostSummaryView>) -> Self {
        IndexTemplate {
            _parent: BaseTemplate::default(),
            posts,
        }
    }
}

#[derive(Template)]
#[template(path = "post.html")]
pub struct PostTemplate<'a> {
    pub _parent: BaseTemplate<'a>,
    pub title: String,
    pub publication_date: String,
    pub back_link: String,
    pub raw_content: String,
}

#[derive(Template)]
#[template(path = "feed.xml")]
pub struct FeedTemplate {
    pub posts: Vec<PostSummaryView>,
}

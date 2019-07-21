use serde::Serialize;

use crate::post::Post;

#[derive(Serialize)]
pub struct DraftLinks {
    #[serde(rename = "self")]
    pub self_: String,
    pub make_public: String,
    pub publish: String,
}

#[derive(Serialize)]
pub struct DraftResource {
    pub title: String,
    pub markdown_content: String,
    pub language: String,
    pub current_slug: Option<String>,
    pub links: DraftLinks,
}

impl DraftResource {
    pub fn from(post: &Post) -> DraftResource {
        return match post {
            Post::Draft { aggregate_id, title, markdown_content, language, shareable, .. } => DraftResource {
                title: title.to_string(),
                markdown_content: markdown_content.to_string(),
                language: language.to_string(),
                current_slug: if *shareable { Some(aggregate_id.to_hyphenated().to_string()) } else { None },
                links: DraftLinks {
                    self_: format!("/api/drafts/{}", aggregate_id.to_hyphenated().to_string()),
                    make_public: format!("/api/drafts/{}/make-public", aggregate_id.to_hyphenated().to_string()),
                    publish: format!("/api/drafts/{}/publish", aggregate_id.to_hyphenated().to_string()),
                },
            },
            Post::Post { .. } => panic!("expected a draft"),
            Post::NonExisting { .. } => panic!("expected a draft"),
        };
    }
}


#[derive(Serialize)]
pub struct PostLinks {
    #[serde(rename = "self")]
    pub self_: String,
    pub view: String,
}

#[derive(Serialize)]
pub struct PostResource {
    pub title: String,
    pub markdown_content: String,
    pub language: String,
    pub publication_date: String,
    pub current_slug: String,
    pub links: PostLinks,
}

impl PostResource {
    pub fn from(post: &Post) -> PostResource {
        return match post {
            Post::Draft { .. } => panic!("expected a post"),
            Post::Post { aggregate_id, title, markdown_content, language, publication_date, current_slug, .. } =>
                PostResource {
                    title: title.clone(),
                    markdown_content: markdown_content.clone(),
                    language: language.to_string(),
                    publication_date: publication_date.to_rfc2822().clone(),
                    current_slug: current_slug.clone(),
                    links: PostLinks {
                        self_: format!("/api/posts/{}", aggregate_id.to_hyphenated().to_string()),
                        view: format!("/posts/{}", current_slug.clone()),
                    },
                },
            Post::NonExisting { .. } => panic!("expected a post"),
        };
    }
}

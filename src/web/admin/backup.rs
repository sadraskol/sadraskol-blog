use actix_web::{Error, HttpResponse, web};
use serde::Serialize;

use crate::pool::Pool;
use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};

#[derive(Serialize)]
struct PostAsJson {
    aggregate_id: String,
    version: u32,
    title: String,
    markdown_content: String,
    language: String,
    shareable: bool,
    publication_date: Option<String>,
    current_slug: Option<String>,
    previous_slugs: Vec<String>,
}

pub async fn get(pool: web::Data<Pool>) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let all_of_them: Vec<PostAsJson> = repo.all().iter()
            .filter_map(|post| {
                match post {
                    Post::NonExisting { .. } => None,
                    Post::Draft { aggregate_id, version, title, markdown_content, language, shareable } => Some(PostAsJson {
                        aggregate_id: aggregate_id.to_hyphenated().to_string(),
                        version: *version,
                        title: title.clone(),
                        markdown_content: markdown_content.to_edit(),
                        language: language.to_string(),
                        shareable: *shareable,
                        publication_date: None,
                        current_slug: None,
                        previous_slugs: vec![],
                    }),
                    Post::Post { aggregate_id, version, title, markdown_content, language, publication_date, current_slug, previous_slugs } => Some(PostAsJson {
                        aggregate_id: aggregate_id.to_hyphenated().to_string(),
                        version: *version,
                        title: title.clone(),
                        markdown_content: markdown_content.to_edit(),
                        language: language.to_string(),
                        shareable: false,
                        publication_date: Some(publication_date.to_rfc3339()),
                        current_slug: Some(current_slug.to_string()),
                        previous_slugs: previous_slugs.clone(),
                    }),
                }
            })
            .collect();
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "application/json; charset=utf-8")
            .json(all_of_them)
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().body(err.to_string())));
}
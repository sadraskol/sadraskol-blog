use actix_web::{Error, HttpResponse, web};
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;

use crate::pool::Pool;
use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};

pub async fn post_by_slug(
    slug: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return repo.find_by_slug(slug.to_string())
            .map(|post| {
                match post {
                    Post::Post { markdown_content, .. } => {
                        let mut options = Options::empty();
                        options.insert(Options::ENABLE_STRIKETHROUGH);
                        let parser = Parser::new_ext(markdown_content.as_str(), options);

                        // Write to String buffer.
                        let mut html_output: String = String::with_capacity(markdown_content.len() * 3 / 2);
                        push_html(&mut html_output, parser);

                        HttpResponse::Ok().body(html_output)
                    }
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""));
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}
use actix_web::{Error, HttpResponse, web};

use crate::pool::Pool;
use crate::post::{ExportedPost, Post};
use crate::post_repository::{PgPostRepository, PostRepository};

pub async fn get(pool: web::Data<Pool>) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let all_of_them: Vec<ExportedPost> = repo.all().iter()
            .filter_map(|post| { post.export_post() })
            .collect();
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "application/json; charset=utf-8")
            .json(all_of_them)
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().body(err.to_string())));
}
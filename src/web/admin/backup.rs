use actix::Addr;
use actix_web::{Error, HttpResponse, web};

use crate::infra::query::Find;
use crate::domain::post::ExportedPost;
use crate::infra::post_repository::PgActor;

pub async fn get(pool: web::Data<Addr<PgActor>>) -> Result<HttpResponse, Error> {
    pool.send(Find::all()).await.unwrap()
        .map(|res| {
            let all_of_them: Vec<ExportedPost> = res.iter()
                .filter_map(|post| { post.export_post() })
                .collect();
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "application/json; charset=utf-8")
                .json(all_of_them)
        })
        .map_err(|err| HttpResponse::InternalServerError().body(err.to_string()).into())
}
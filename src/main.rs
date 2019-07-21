extern crate actix_web;

use std::str::FromStr;

use actix_web::{App, HttpResponse, HttpServer, Responder, web};
use actix_web::middleware::Logger;
use env_logger;
use postgres::Connection;
use pulldown_cmark::{html, Parser};
use serde::Deserialize;

use pool::Pool;
use post::Post;
use post_repository::{PgPostRepository, PostRepository};

mod pool;
mod post;
mod post_repository;

fn index(pool: web::Data<Pool>) -> impl Responder {
    let conn: &Connection = &pool.get().unwrap();
    let repo = PgPostRepository::new(conn);
    let all_sections: Vec<String> = repo.find()
        .iter()
        .map(|post| {
            let markdown_input = match post {
                Post::Draft { markdown_content, .. } => markdown_content.clone(),
                Post::Post { markdown_content, .. } => markdown_content.clone(),
                Post::NonExisting { .. } => "".to_string(),
            };
            let parser = Parser::new(&*markdown_input);

            let mut html_output = String::new();
            html::push_html(&mut html_output, parser);
            return html_output;
        })
        .collect();
    return HttpResponse::Ok()
        .body("<html><section>".to_owned() + &*all_sections.join("</section><section>") + "</section></html>");
}

fn list_drafts(pool: web::Data<Pool>) -> impl Responder {
    let conn: &Connection = &pool.get().unwrap();
    let repo = PgPostRepository::new(conn);
    let all_sections: Vec<String> = repo.all_drafts()
        .iter()
        .map(|post| {
            let markdown_input = match post {
                Post::Draft { markdown_content, .. } => markdown_content.clone(),
                Post::Post { markdown_content, .. } => markdown_content.clone(),
                Post::NonExisting { .. } => "".to_string(),
            };
            let parser = Parser::new(&*markdown_input);

            let mut html_output = String::new();
            html::push_html(&mut html_output, parser);
            return html_output;
        })
        .collect();
    return HttpResponse::Ok()
        .body("<html><section>".to_owned() + &*all_sections.join("</section><section>") + "</section></html>");
}

#[derive(Deserialize)]
pub struct SubmitDraft {
    language: String,
    title: String,
    description: String,
    markdown_content: String,
}

fn submit_draft(
    params: web::Json<SubmitDraft>,
    pool: web::Data<Pool>,
) -> impl Responder {
    let conn: &Connection = &pool.get().unwrap();
    let mut repo = PgPostRepository::new(conn);

    let draft = Post::NonExisting { aggregate_id: uuid::Uuid::new_v4() };
    let parameters = params.into_inner();
    let result = draft.submit_draft(
        FromStr::from_str(parameters.language.as_str()).unwrap(),
        parameters.title.to_owned(),
        parameters.description.to_owned(),
        parameters.markdown_content.to_owned(),
    );
    return match result {
        Ok(new_draft) => {
            repo.submit_draft(new_draft.clone());
            return HttpResponse::Ok().json(new_draft.aggregate_id);
        }
        Err(err) => HttpResponse::Forbidden().json(err.to_string()),
    };
}


fn main() {
    std::env::set_var("RUST_LOG", "actix_web=info");
    env_logger::init();

    let manager = pool::ConnectionManager::new("postgres://postgres:postgres@localhost:5432/sadraskol_dev");
    let pool: pool::Pool = r2d2::Pool::builder()
        .build(manager)
        .expect("Failed to create pool.");

    HttpServer::new(move || App::new()
        .data(pool.clone())
        .wrap(Logger::default())
        .service(
            web::scope("/")
                .route("", web::get().to(index))
                .route("/api/v2/drafts", web::get().to(list_drafts))
                .route("/api/v2/drafts", web::put().to(submit_draft))
            // .route("/api/v2/drafts/:draft_id", web::get().to(show_draft))
            // .route("/api/v2/drafts/:draft_id/make-public", web::post().to(make_draft_public))
            // .route("/api/v2/drafts/:draft_id", web::patch().to(edit_draft))
            // .route("/api/v2/drafts/:draft_id", web::delete().to(delete_draft))
        ))
        .bind("127.0.0.1:4000")
        .unwrap()
        .run()
        .unwrap();
}

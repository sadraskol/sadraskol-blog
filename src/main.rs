extern crate actix_web;

use std::collections::BTreeMap;
use std::ops::Deref;

use actix_web::{App, Error, HttpResponse, HttpServer, Responder, web};
use actix_web::middleware::Compress;
use actix_web::middleware::Logger;
use env_logger;
use handlebars::Handlebars;
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;
use serde_json::to_value;

use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};
use std::time::Duration;

pub mod api;
pub mod pool;
pub mod post;
pub mod post_repository;
pub mod slugify;
pub mod config;

async fn dist(filename: web::Path<String>) -> Result<HttpResponse, Error> {
    let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("front");
    d.push("dist");
    d.push(filename.into_inner());
    Ok(serve_file(d))
}

async fn index(hb: web::Data<Handlebars<'_>>) -> Result<HttpResponse, Error> {
    let mut map = BTreeMap::new();
    map.insert("some", "value");
    let data = to_value(map).unwrap();
    let body = hb.render("index", &data).unwrap();
    Ok(HttpResponse::Ok().body(body))
}

fn serve_file(d: std::path::PathBuf) -> HttpResponse {
    std::fs::read_to_string(d)
        .map(|content| {
            HttpResponse::Ok().body(content)
        })
        .unwrap_or(HttpResponse::NotFound().body(""))
}

async fn health(pool: web::Data<pool::Pool>) -> impl Responder {
    pool.get()
        .map_err(|_| "no connection in pool".to_string())
        .and_then(|mut connection| connection.query("values (1)", &[])
            .map_err(|_| "query failed".to_string()))
        .map(|_| HttpResponse::Ok().body(""))
        .unwrap_or_else(|err| HttpResponse::InternalServerError().body(err))
}

pub async fn post_by_slug(
    slug: web::Path<String>,
    pool: web::Data<pool::Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.deref(), |repo| {
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
                    },
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""));
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

#[actix_rt::main]
async fn main() -> std::io::Result<()> {
    std::env::set_var("RUST_LOG", "actix_server=info,actix_web=info");
    env_logger::init();

    let config = config::cfg();

    let pool: pool::Pool = r2d2::Pool::builder()
        .connection_timeout(Duration::from_secs(4))
        .build(pool::ConnectionManager::new(config.postgres.clone()))
        .expect("Failed to create pool");

    let mut handlebars: Handlebars<'_> = Handlebars::new();
    handlebars.register_template_file("index", "./front/templates/index.html").unwrap();
    let hb_ref = web::Data::new(handlebars);

    let listen_address = format!("{}:{}", config.host, config.port);
    HttpServer::new(move || {
        App::new()
            .data(pool.clone())
            .app_data(hb_ref.clone())
            .wrap(Compress::default())
            .wrap(Logger::default())
            .service(web::scope("/api")
                .service(
                    web::resource("/drafts")
                        .route(web::get().to(api::list_drafts))
                        .route(web::put().to(api::submit_draft)))
                .service(web::resource("/drafts/{draft_id}")
                    .route(web::get().to(api::show_draft))
                    .route(web::patch().to(api::edit_draft))
                    .route(web::delete().to(api::delete_draft)))
                .service(web::resource("/drafts/{draft_id}/make-public").route(web::post().to(api::make_draft_public)))
                .service(web::resource("/drafts/{draft_id}/publish").route(web::post().to(api::publish_draft)))
                .service(web::resource("/posts").route(web::get().to(api::list_posts)))
                .service(web::resource("/posts/{post_id}").route(web::patch().to(api::edit_post)))
            )
            .service(web::resource("/health").route(web::get().to(health)))
            .service(web::resource("/").route(web::get().to(index)))
            .service(web::resource("/drafts").route(web::get().to(index)))
            .service(web::resource("/posts").route(web::get().to(index)))
            .service(web::resource("/posts/{slug:.*}").route(web::get().to(post_by_slug)))
            .service(web::resource("/dist/{filename:.*}").route(web::get().to(dist)))
    })
        .bind(listen_address.clone())?.run()
        .await
}

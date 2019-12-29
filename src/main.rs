extern crate actix_web;

use std::time::Duration;

use actix_web::{App, HttpServer};
use actix_web::middleware::Compress;
use actix_web::middleware::Logger;
use env_logger;
use handlebars::Handlebars;

use crate::identity::{CheckAdmin, identity_service};
use crate::web::post::post_by_slug;

pub mod api;
pub mod web;
pub mod identity;
pub mod pool;
pub mod post;
pub mod post_repository;
pub mod slugify;
pub mod config;

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
    let hb_ref = actix_web::web::Data::new(handlebars);

    let listen_address = format!("{}:{}", config.host, config.port);
    HttpServer::new(move || {
        App::new()
            .data(pool.clone())
            .app_data(hb_ref.clone())
            .wrap(identity_service())
            .wrap(Compress::default())
            .wrap(Logger::default())
            .service(actix_web::web::scope("/api")
                .wrap(CheckAdmin {})
                .service(
                    actix_web::web::resource("/drafts")
                        .route(actix_web::web::get().to(api::list_drafts))
                        .route(actix_web::web::put().to(api::submit_draft)))
                .service(actix_web::web::resource("/drafts/{draft_id}")
                    .route(actix_web::web::get().to(api::show_draft))
                    .route(actix_web::web::patch().to(api::edit_draft))
                    .route(actix_web::web::delete().to(api::delete_draft)))
                .service(actix_web::web::resource("/drafts/{draft_id}/make-public").route(actix_web::web::post().to(api::make_draft_public)))
                .service(actix_web::web::resource("/drafts/{draft_id}/publish").route(actix_web::web::post().to(api::publish_draft)))
                .service(actix_web::web::resource("/posts").route(actix_web::web::get().to(api::list_posts)))
                .service(actix_web::web::resource("/posts/{post_id}").route(actix_web::web::patch().to(api::edit_post)))
            )
            .service(actix_web::web::resource("/login").route(actix_web::web::get().to(web::login)))
            .service(actix_web::web::resource("/health").route(actix_web::web::get().to(web::health)))
            .service(actix_web::web::resource("/").wrap(CheckAdmin {}).route(actix_web::web::get().to(web::index)))
            .service(actix_web::web::resource("/drafts").wrap(CheckAdmin {}).route(actix_web::web::get().to(web::index)))
            .service(actix_web::web::resource("/posts").wrap(CheckAdmin {}).route(actix_web::web::get().to(web::index)))
            .service(actix_web::web::resource("/posts/{slug:.*}").route(actix_web::web::get().to(post_by_slug)))
            .service(actix_web::web::resource("/dist/{filename:.*}").route(actix_web::web::get().to(web::dist)))
    })
        .bind(listen_address.clone())?.run()
        .await
}
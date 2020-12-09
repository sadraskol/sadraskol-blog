use actix::Addr;
use actix_identity::Identity;
use actix_web::http::header::LOCATION;
use actix_web::{web, Error, HttpResponse, Responder};
use askama::Template;
use serde::{Deserialize, Serialize};

use crate::config;
use crate::infra::health::Health;
use crate::infra::post_repository::PgActor;

pub mod admin;
pub mod identity;
pub mod post;

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
#[template(path = "login.html")]
struct LoginTemplate<'a> {
    _parent: BaseTemplate<'a>,
}

pub async fn login() -> Result<HttpResponse, Error> {
    let template = LoginTemplate {
        _parent: BaseTemplate::default(),
    };
    Ok(HttpResponse::Ok()
        .header(
            actix_web::http::header::CONTENT_TYPE,
            "text/html; charset=utf-8",
        )
        .body(template.render().unwrap()))
}

#[derive(Serialize, Deserialize)]
pub struct LoginForm {
    login: String,
    password: String,
}

pub async fn submit_login(
    params: web::Form<LoginForm>,
    id: Identity,
) -> Result<HttpResponse, Error> {
    let config = config::cfg();
    if config.admin.login == params.login && config.admin.password == params.password {
        id.remember("admin".to_string());
        Ok(HttpResponse::Found().header(LOCATION, "/admin").body(""))
    } else {
        Ok(HttpResponse::Unauthorized().header(LOCATION, "/").body(""))
    }
}

pub async fn dist(filename: web::Path<String>) -> Result<HttpResponse, Error> {
    let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("front");
    d.push("dist");
    d.push(filename.into_inner());
    Ok(serve_file(d))
}

fn serve_file(d: std::path::PathBuf) -> HttpResponse {
    std::fs::read_to_string(d)
        .map(|content| HttpResponse::Ok().body(content))
        .unwrap_or_else(|_| HttpResponse::NotFound().body(""))
}

pub async fn health(addr: web::Data<Addr<PgActor>>) -> impl Responder {
    addr.send(Health::new())
        .await
        .map_err(|err| HttpResponse::InternalServerError().body(err.to_string()))
        .and_then(|result| {
            result
                .map(|_| HttpResponse::Ok().body(""))
                .map_err(|err| HttpResponse::InternalServerError().body(err.to_string()))
        })
}

pub async fn favicon() -> impl Responder {
    let favico: &[u8; 339] = include_bytes!("favicon.png");
    HttpResponse::Ok()
        .header("content-type", "image/png")
        .body(favico.to_vec())
}
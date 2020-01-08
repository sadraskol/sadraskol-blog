use actix_identity::Identity;
use actix_web::{Error, HttpResponse, Responder, web};
use actix_web::http::header::LOCATION;
use askama::Template;
use serde::{Deserialize, Serialize};

use crate::config;
use crate::pool::Pool;

pub mod post;
pub mod admin;

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
    _parent: BaseTemplate<'a>
}

pub async fn login() -> Result<HttpResponse, Error> {
    let template = LoginTemplate {
        _parent: BaseTemplate::default()
    };
    Ok(HttpResponse::Ok()
        .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
        .body(template.render().unwrap()))
}

#[derive(Serialize, Deserialize)]
pub struct LoginForm {
    login: String,
    password: String,
}

pub async fn submit_login(params: web::Form<LoginForm>, id: Identity) -> Result<HttpResponse, Error> {
    let config = config::cfg();
    if config.admin.login == params.login && config.admin.password == params.password {
        id.remember("admin".to_string());
        Ok(HttpResponse::Found().header(LOCATION, "/admin").body(""))
    } else {
        Ok(HttpResponse::Found().header(LOCATION, "/").body(""))
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
        .map(|content| {
            HttpResponse::Ok().body(content)
        })
        .unwrap_or(HttpResponse::NotFound().body(""))
}

pub async fn health(pool: web::Data<Pool>) -> impl Responder {
    pool.get()
        .map_err(|_| "no connection in pool".to_string())
        .and_then(|mut connection| connection.query("values (1)", &[])
            .map_err(|_| "query failed".to_string()))
        .map(|_| HttpResponse::Ok().body(""))
        .unwrap_or_else(|err| HttpResponse::InternalServerError().body(err))
}
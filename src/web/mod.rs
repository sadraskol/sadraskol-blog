use actix::Addr;
use actix_identity::Identity;
use actix_web::{Error, HttpResponse, Responder, web};
use actix_web::http::header::LOCATION;
use askama::Template;
use serde::{Deserialize, Serialize};

use crate::config;
use crate::infra::health::Health;
use crate::post_repository::DbExecutor;

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

pub async fn health(
    addr: web::Data<Addr<DbExecutor>>
) -> impl Responder {
    addr.send(Health::new())
        .await
        .map_err(|err| HttpResponse::InternalServerError().body(err.to_string()).into())
        .and_then(|result| {
            result.map(|_| HttpResponse::Ok().body(""))
                .map_err(|err| HttpResponse::InternalServerError().body(err.to_string()))
        })
}
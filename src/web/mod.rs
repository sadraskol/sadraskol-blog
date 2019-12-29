use std::collections::BTreeMap;

use actix_identity::Identity;
use actix_web::{Error, HttpResponse, Responder, web};
use handlebars::Handlebars;
use serde_json::to_value;

use crate::pool::Pool;

pub mod post;

pub async fn login(id: Identity) -> Result<HttpResponse, Error> {
    id.remember("admin".to_owned());
    Ok(HttpResponse::Ok().body(""))
}

pub async fn dist(filename: web::Path<String>) -> Result<HttpResponse, Error> {
    let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("front");
    d.push("dist");
    d.push(filename.into_inner());
    Ok(serve_file(d))
}

pub async fn index(hb: web::Data<Handlebars<'_>>) -> Result<HttpResponse, Error> {
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

pub async fn health(pool: web::Data<Pool>) -> impl Responder {
    pool.get()
        .map_err(|_| "no connection in pool".to_string())
        .and_then(|mut connection| connection.query("values (1)", &[])
            .map_err(|_| "query failed".to_string()))
        .map(|_| HttpResponse::Ok().body(""))
        .unwrap_or_else(|err| HttpResponse::InternalServerError().body(err))
}
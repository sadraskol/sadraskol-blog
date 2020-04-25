use actix::Addr;
use actix_web::{Error, HttpResponse, web};
use askama::Template;
use chrono::{DateTime, Utc};

use crate::infra::query::{Find, FindBy};
use crate::domain::post::Post;
use crate::infra::post_repository::PgActor;
use crate::web::BaseTemplate;

#[derive(Template)]
#[template(path = "post.html")]
struct PostTemplate<'a> {
    _parent: BaseTemplate<'a>,
    title: String,
    publication_date: String,
    back_link: String,
    raw_content: String,
}

pub async fn post_by_slug(
    slug: web::Path<String>,
    addr: web::Data<Addr<PgActor>>,
) -> Result<HttpResponse, Error> {
    addr.send(FindBy::slug(slug.to_string())).await.unwrap()
        .map(|res| {
            res.map(|post| {
                match post {
                    Post::Post { markdown_content, title, current_slug, publication_date, .. } => {
                        if current_slug != slug.to_string() {
                            HttpResponse::Found()
                                .header(actix_web::http::header::LOCATION, format!("/posts/{}", current_slug))
                                .body("")
                        } else {
                            let page = PostTemplate {
                                _parent: BaseTemplate::default(),
                                title: title.clone(),
                                publication_date: publication_date.format("%d %B %Y").to_string(),
                                back_link: "/".to_string(),
                                raw_content: markdown_content.format(),
                            };

                            HttpResponse::Ok()
                                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                                .body(page.render().unwrap())
                        }
                    }
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""))
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

pub struct PostSummaryView {
    title: String,
    publication_date: String,
    language: String,
    view_link: String,
}

impl PostSummaryView {
    fn for_human(post: &Post) -> PostSummaryView {
        Self::from(post, |d| d.format("%d %B %Y").to_string())
    }
    fn for_machine(post: &Post) -> PostSummaryView {
        Self::from(post, |d| d.to_rfc3339())
    }
    fn from<F: FnOnce(&DateTime<Utc>) -> String>(post: &Post, f: F) -> PostSummaryView {
        match post {
            Post::Draft { .. } => panic!("expected a post"),
            Post::Post { title, publication_date, current_slug, language, .. } =>
                PostSummaryView {
                    title: title.clone(),
                    language: language.to_string(),
                    publication_date: f(publication_date),
                    view_link: format!("/posts/{}", current_slug.clone()),
                },
            Post::NonExisting { .. } => panic!("expected a post"),
        }
    }
}

#[derive(Template)]
#[template(path = "index.html")]
struct IndexTemplate<'a> {
    _parent: BaseTemplate<'a>,
    posts: Vec<PostSummaryView>,
}

pub async fn index(
    addr: web::Data<Addr<PgActor>>,
) -> Result<HttpResponse, Error> {
    addr.send(Find::posts())
        .await.unwrap()
        .map(|res| {
            let posts = res
                .iter()
                .map(PostSummaryView::for_human)
                .collect();
            let template = IndexTemplate { _parent: BaseTemplate::default(), posts };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Template)]
#[template(path = "feed.xml")]
struct FeedTemplate {
    posts: Vec<PostSummaryView>
}

pub async fn feed(
    addr: web::Data<Addr<PgActor>>,
) -> Result<HttpResponse, Error> {
    addr.send(Find::posts()).await.unwrap()
        .map(|res| {
            let posts = res.iter()
                .map(PostSummaryView::for_machine)
                .collect();
            let template = FeedTemplate { posts };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "application/rss+xml; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}
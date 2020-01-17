use actix_web::{Error, HttpResponse, web};
use askama::Template;
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;

use crate::pool::Pool;
use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};
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
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return repo.find_by_slug(slug.to_string())
            .map(|post| {
                match post {
                    Post::Post { markdown_content, title, current_slug, publication_date, .. } => {
                        if current_slug != slug.to_string() {
                            HttpResponse::Found()
                                .header(actix_web::http::header::LOCATION, format!("/posts/{}", current_slug))
                                .body("")
                        } else {
                            let mut options = Options::empty();
                            options.insert(Options::ENABLE_STRIKETHROUGH);
                            let parser = Parser::new_ext(markdown_content.as_str(), options);

                            // Write to String buffer.
                            let mut html_output: String = String::with_capacity(markdown_content.len() * 3 / 2);
                            push_html(&mut html_output, parser);

                            let page = PostTemplate {
                                _parent: BaseTemplate::default(),
                                title: title.clone(),
                                publication_date:publication_date.format("%d %B %Y").to_string(),
                                back_link: "/".to_string(),
                                raw_content: html_output.clone(),
                            };

                            HttpResponse::Ok()
                                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                                .body(page.render().unwrap())
                        }
                    }
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""));
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub struct PostSummaryView {
    title: String,
    publication_date: String,
    language: String,
    view_link: String,
}

impl PostSummaryView {
    fn from(post: &Post) -> PostSummaryView {
        match post {
            Post::Draft { .. } => panic!("expected a post"),
            Post::Post { title, publication_date, current_slug, language, .. } =>
                PostSummaryView {
                    title: title.clone(),
                    language: language.to_string(),
                    publication_date: publication_date.format("%d %B %Y").to_string(),
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
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let posts = repo.all_posts()
            .iter()
            .map(PostSummaryView::from)
            .collect();
        let template = IndexTemplate { _parent: BaseTemplate::default(), posts };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
            .body(template.render().unwrap())
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())))
}

#[derive(Template)]
#[template(path = "feed.xml")]
struct FeedTemplate {
    posts: Vec<PostSummaryView>
}

pub async fn feed(
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let posts = repo.all_posts()
            .iter()
            .map(PostSummaryView::from)
            .collect();
        let template = FeedTemplate { posts };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "application/rss+xml; charset=utf-8")
            .body(template.render().unwrap())
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())))
}
use actix_web::{Error, HttpResponse, web};
use askama::Template;
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;

use crate::pool::Pool;
use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};

#[derive(Template)]
#[template(path = "post.html")]
struct PostTemplate {
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
                    Post::Post { markdown_content, .. } => {
                        let mut options = Options::empty();
                        options.insert(Options::ENABLE_STRIKETHROUGH);
                        let parser = Parser::new_ext(markdown_content.as_str(), options);

                        // Write to String buffer.
                        let mut html_output: String = String::with_capacity(markdown_content.len() * 3 / 2);
                        push_html(&mut html_output, parser);

                        let page = PostTemplate { raw_content: html_output.clone() };

                        HttpResponse::Ok().body(page.render().unwrap())
                    }
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""));
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub struct PostSummaryView {
    title: String,
    publication_date: String,
    view_link: String,
}

impl PostSummaryView {
    fn from(post: &Post) -> PostSummaryView {
        match post {
            Post::Draft { .. } => panic!("expected a post"),
            Post::Post { title, publication_date, current_slug, .. } =>
                PostSummaryView {
                    title: title.clone(),
                    publication_date: publication_date.format("%d %B %Y").to_string(),
                    view_link: format!("/posts/{}", current_slug.clone()),
                },
            Post::NonExisting { .. } => panic!("expected a post"),
        }
    }
}


#[derive(Template)]
#[template(path = "index.html")]
struct IndexTemplate {
    posts: Vec<PostSummaryView>
}

pub async fn index(
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let posts = repo.all_posts()
            .iter()
            .map(PostSummaryView::from)
            .collect();
        let template = IndexTemplate { posts };
        HttpResponse::Ok().body(template.render().unwrap())
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())))
}
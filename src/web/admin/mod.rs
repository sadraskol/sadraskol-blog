use actix_web::{Error, HttpResponse, web};
use askama::Template;
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;
use uuid::Uuid;

use crate::pool::Pool;
use crate::post::Post;
use crate::post_repository::{PgPostRepository, PostRepository};
use crate::web::BaseTemplate;

pub async fn index() -> Result<HttpResponse, Error> {
    Ok(HttpResponse::Found()
        .header(actix_web::http::header::LOCATION, "/admin/drafts")
        .body(""))
}

pub struct DraftSummaryView {
    title: String,
    markdown_content: String,
    language: String,
    preview_link: String,
    edit_link: String,
    publish_link: String,
    public_yet: bool,
    make_public_link: String,
}

impl DraftSummaryView {
    fn from(post: &Post) -> DraftSummaryView {
        match post {
            Post::NonExisting { .. } => panic!("not a draft"),
            Post::Draft { title, aggregate_id, markdown_content, language, shareable, .. } => DraftSummaryView {
                title: title.clone(),
                markdown_content: markdown_content.to_string(),
                language: language.to_string(),
                preview_link: format!("/admin/drafts/{}/preview", aggregate_id.to_hyphenated().to_string()),
                edit_link: format!("/admin/drafts/{}", aggregate_id.to_hyphenated().to_string()),
                publish_link: format!("/admin/drafts/{}/publish", aggregate_id.to_hyphenated().to_string()),
                public_yet: shareable.clone(),
                make_public_link: format!("/admin/drafts/{}/make-public", aggregate_id.to_hyphenated().to_string()),
            },
            Post::Post { .. } => panic!("not a draft"),
        }
    }
}

#[derive(Template)]
#[template(path = "admin/drafts.html")]
struct DraftsTemplate<'a> {
    _parent: BaseTemplate<'a>,
    drafts: Vec<DraftSummaryView>,
}

pub async fn drafts(
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let drafts = repo.all_drafts()
            .iter()
            .map(DraftSummaryView::from)
            .collect();
        let template = DraftsTemplate { _parent: BaseTemplate::default(), drafts };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
            .body(template.render().unwrap())
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())))
}

#[derive(Template)]
#[template(path = "admin/edit_draft.html")]
struct EditDraftTemplate<'a> {
    _parent: BaseTemplate<'a>,
    draft: DraftSummaryView,
}

pub async fn draft(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo|
        Uuid::parse_str(&*draft_id).ok()
            .and_then(|i| repo.read(i))
            .map(|d| DraftSummaryView::from(&d))
            .map(|draft| {
                let template = EditDraftTemplate { _parent: BaseTemplate::default(), draft };
                HttpResponse::Ok()
                    .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                    .body(template.render().unwrap())
            })
            .unwrap_or(HttpResponse::NotFound()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body("")),
    )
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}


#[derive(Template)]
#[template(path = "post.html")]
struct DraftPreviewTemplate<'a> {
    _parent: BaseTemplate<'a>,
    raw_content: String,
}

pub async fn preview_draft(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return Uuid::parse_str(&*draft_id).ok()
            .and_then(|i| repo.read(i))
            .map(|post| {
                match post {
                    Post::Draft { markdown_content, .. } => {
                        let mut options = Options::empty();
                        options.insert(Options::ENABLE_STRIKETHROUGH);
                        let parser = Parser::new_ext(markdown_content.as_str(), options);

                        // Write to String buffer.
                        let mut html_output: String = String::with_capacity(markdown_content.len() * 3 / 2);
                        push_html(&mut html_output, parser);

                        let page = DraftPreviewTemplate { _parent: BaseTemplate::default(), raw_content: html_output.clone() };

                        HttpResponse::Ok()
                            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                            .body(page.render().unwrap())
                    }
                    _ => HttpResponse::NotFound().json(""),
                }
            }).unwrap_or(HttpResponse::NotFound().json(""));
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}
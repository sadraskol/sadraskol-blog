use std::str::FromStr;

use actix::Addr;
use actix_web::{Error, HttpResponse, web};
use askama::Template;
use serde::Deserialize;
use uuid::Uuid;

use crate::infra::command::Command;
use crate::infra::query::{Find, FindBy};
use crate::post::{AggregateId, Post};
use crate::post::PostEvent;
use crate::post_repository::DbExecutor;
use crate::web::BaseTemplate;

pub mod backup;

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
            Post::NonExisting { .. } => DraftSummaryView {
                title: "".to_string(),
                markdown_content: "".to_string(),
                language: "fr".to_string(),
                preview_link: format!("/admin/drafts/{}/preview", "new"),
                edit_link: format!("/admin/drafts/{}", "new"),
                publish_link: format!("/admin/drafts/{}/publish", "new"),
                public_yet: false,
                make_public_link: format!("/admin/drafts/{}/make-public", "new"),
            },
            Post::Draft { title, aggregate_id, markdown_content, language, shareable, .. } => DraftSummaryView {
                title: title.clone(),
                markdown_content: markdown_content.to_edit(),
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
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    addr.send(Find::drafts()).await.unwrap()
        .map(|res| {
            let drafts = res.iter()
                .map(DraftSummaryView::from)
                .collect();
            let template = DraftsTemplate { _parent: BaseTemplate::default(), drafts };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Template)]
#[template(path = "admin/edit_draft.html")]
struct EditDraftTemplate<'a> {
    _parent: BaseTemplate<'a>,
    draft: DraftSummaryView,
}

pub async fn draft(
    draft_id: web::Path<String>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(draft_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(FindBy::id(id))
        .await.unwrap()
        .map(|res| {
            let post = res.unwrap_or(Post::NonExisting { aggregate_id: id });
            let draft_view = DraftSummaryView::from(&post);

            let template = EditDraftTemplate { _parent: BaseTemplate::default(), draft: draft_view };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Deserialize)]
pub struct SubmitDraftForm {
    pub language: String,
    pub title: String,
    pub markdown_content: String,
}

pub async fn edit_draft(
    draft_id: web::Path<String>,
    params: web::Form<SubmitDraftForm>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(draft_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(Command::SubmitDraft(
        id,
        FromStr::from_str(params.language.as_str()).unwrap(),
        params.title.clone(),
        params.markdown_content.clone(),
    )).await.unwrap()
        .map(|e| event_response(id, e))
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Template)]
#[template(path = "post.html")]
struct DraftPreviewTemplate<'a> {
    _parent: BaseTemplate<'a>,
    title: String,
    publication_date: String,
    back_link: String,
    raw_content: String,
}

pub async fn preview_draft(
    draft_id: web::Path<String>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(draft_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(FindBy::id(id))
        .await.unwrap()
        .map(|res| {
            let post = res.unwrap_or(Post::NonExisting { aggregate_id: id });
            match post {
                Post::Draft { aggregate_id, markdown_content, title, .. } => {
                    let page = DraftPreviewTemplate {
                        _parent: BaseTemplate::default(),
                        title: title.clone(),
                        publication_date: chrono::Utc::now().format("%d %B %Y").to_string(),
                        back_link: format!("/admin/drafts/{}", aggregate_id.to_hyphenated().to_string()),
                        raw_content: markdown_content.format(),
                    };

                    HttpResponse::Ok()
                        .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                        .body(page.render().unwrap())
                }
                _ => HttpResponse::NotFound().json(""),
            }
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

pub async fn publish_draft(
    draft_id: web::Path<String>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(draft_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(Command::PublishDraft(id, chrono::Utc::now()))
        .await.unwrap()
        .map(|e| event_response(id, e))
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

pub async fn make_draft_public(
    draft_id: web::Path<String>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(draft_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(Command::MakePublic(id))
        .await.unwrap()
        .map(|e| event_response(id, e))
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

pub struct PostSummaryView {
    title: String,
    markdown_content: String,
    language: String,
    publication_date: String,
    self_link: String,
    edit_link: String,
}

impl PostSummaryView {
    fn from(post: &Post) -> PostSummaryView {
        match post {
            Post::Post { title, aggregate_id, markdown_content, language, publication_date, current_slug, .. } => PostSummaryView {
                title: title.clone(),
                markdown_content: markdown_content.to_edit(),
                language: language.to_string(),
                publication_date: publication_date.format("%d %B %Y").to_string(),
                edit_link: format!("/admin/posts/{}", aggregate_id.to_hyphenated().to_string()),
                self_link: format!("/posts/{}", current_slug.clone()),
            },
            _ => panic!("not a draft"),
        }
    }
}

#[derive(Template)]
#[template(path = "admin/posts.html")]
struct PostsTemplate<'a> {
    _parent: BaseTemplate<'a>,
    posts: Vec<PostSummaryView>,
}

pub async fn posts(
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    addr.send(Find::posts()).await.unwrap()
        .map(|res| {
            let posts = res.iter()
                .map(PostSummaryView::from)
                .collect();
            let template = PostsTemplate { _parent: BaseTemplate::default(), posts };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Template)]
#[template(path = "admin/edit_post.html")]
struct EditPostTemplate<'a> {
    _parent: BaseTemplate<'a>,
    post: PostSummaryView,
}

pub async fn post(
    post_id: web::Path<String>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(post_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(FindBy::id(id))
        .await.unwrap()
        .map(|res| {
            let post = res.unwrap_or(Post::NonExisting { aggregate_id: id });
            let post_view = PostSummaryView::from(&post);

            let template = EditPostTemplate { _parent: BaseTemplate::default(), post: post_view };
            HttpResponse::Ok()
                .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                .body(template.render().unwrap())
        })
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

#[derive(Deserialize)]
pub struct EditPostForm {
    pub language: String,
    pub title: String,
    pub markdown_content: String,
}

pub async fn edit_post(
    post_id: web::Path<String>,
    params: web::Form<EditPostForm>,
    addr: web::Data<Addr<DbExecutor>>,
) -> Result<HttpResponse, Error> {
    let id = Uuid::parse_str(post_id.as_str())
        .unwrap_or(Uuid::new_v4());

    addr.send(Command::EditPost(
        id,
        FromStr::from_str(params.language.as_str()).unwrap(),
        params.title.clone(),
        params.markdown_content.clone(),
    ))
        .await.unwrap()
        .map(|e| event_response(id, e))
        .map_err(|err| HttpResponse::InternalServerError().json(err.to_string()).into())
}

fn event_response(id: AggregateId, e: PostEvent) -> HttpResponse {
    let id_str = id.to_hyphenated().to_string();
    match e {
        PostEvent::DraftDeleted(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin/drafts"))
            .body(""),
        PostEvent::DraftSubmitted(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", id_str))
            .body(""),
        PostEvent::DraftMadePublic(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", id_str))
            .body(""),
        PostEvent::PostPublished(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin/posts/{}", id_str))
            .body(""),
        PostEvent::PostEdited(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin/posts/{}", id_str))
            .body(""),
        PostEvent::PostError(_) => HttpResponse::Found()
            .header(actix_web::http::header::LOCATION, format!("/admin"))
            .body("")
    }
}
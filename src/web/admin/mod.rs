use std::str::FromStr;

use actix_web::{Error, HttpResponse, web};
use askama::Template;
use pulldown_cmark::{Options, Parser};
use pulldown_cmark::html::push_html;
use serde::Deserialize;
use uuid::Uuid;

use crate::pool::Pool;
use crate::post::Post;
use crate::post::PostEvent;
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
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let post = find_post(repo, draft_id.clone());
        let draft_view = DraftSummaryView::from(&post);

        let template = EditDraftTemplate { _parent: BaseTemplate::default(), draft: draft_view };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
            .body(template.render().unwrap())
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
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
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let draft = find_post(repo, draft_id.clone());
        let event = draft.submit_draft(
            FromStr::from_str(params.language.as_str()).unwrap(),
            params.title.to_owned(),
            params.markdown_content.to_owned(),
        );
        repo.save(event.clone());
        match event {
            PostEvent::DraftSubmitted(_) => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", draft.aggregate_id().clone()))
                .body(""),
            _ => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", draft_id.clone()))
                .body("")
        }
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

#[derive(Template)]
#[template(path = "post.html")]
struct DraftPreviewTemplate<'a> {
    _parent: BaseTemplate<'a>,
    title: String,
    back_link: String,
    raw_content: String,
}

pub async fn preview_draft(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let post = find_post(repo, draft_id.clone());
        match post {
            Post::Draft { aggregate_id, markdown_content, title, .. } => {
                let mut options = Options::empty();
                options.insert(Options::ENABLE_STRIKETHROUGH);
                let parser = Parser::new_ext(markdown_content.as_str(), options);

                let mut html_output: String = String::with_capacity(markdown_content.len() * 3 / 2);
                push_html(&mut html_output, parser);

                let page = DraftPreviewTemplate {
                    _parent: BaseTemplate::default(),
                    title: title.clone(),
                    back_link: format!("/admin/drafts/{}", aggregate_id.to_hyphenated().to_string()),
                    raw_content: html_output.clone(),
                };

                HttpResponse::Ok()
                    .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
                    .body(page.render().unwrap())
            }
            _ => HttpResponse::NotFound().json(""),
        }
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn publish_draft(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let draft = find_post(repo, draft_id.clone());
        let event = draft.publish_draft(chrono::Utc::now());
        repo.save(event.clone());
        match event {
            PostEvent::PostPublished(_) => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/posts/{}", draft.aggregate_id().clone()))
                .body(""),
            _ => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", draft_id.clone()))
                .body("")
        }
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn make_draft_public(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let draft = find_post(repo, draft_id.clone());
        let event = draft.make_public();
        repo.save(event.clone());
        match event {
            PostEvent::DraftMadePublic(_) => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", draft.aggregate_id().clone()))
                .body(""),
            _ => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/drafts/{}", draft_id.clone()))
                .body("")
        }
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

fn find_post(repo: &mut PgPostRepository, draft_id: String) -> Post {
    Uuid::parse_str(draft_id.as_str()).ok()
        .and_then(|i| repo.read(i))
        .unwrap_or(Post::NonExisting { aggregate_id: uuid::Uuid::new_v4() })
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
                markdown_content: markdown_content.to_string(),
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
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let posts = repo.all_posts()
            .iter()
            .map(PostSummaryView::from)
            .collect();
        let template = PostsTemplate { _parent: BaseTemplate::default(), posts };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
            .body(template.render().unwrap())
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())))
}

#[derive(Template)]
#[template(path = "admin/edit_post.html")]
struct EditPostTemplate<'a> {
    _parent: BaseTemplate<'a>,
    post: PostSummaryView,
}

pub async fn post(
    post_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let post = find_post(repo, post_id.clone());
        let post_view = PostSummaryView::from(&post);

        let template = EditPostTemplate { _parent: BaseTemplate::default(), post: post_view };
        HttpResponse::Ok()
            .header(actix_web::http::header::CONTENT_TYPE, "text/html; charset=utf-8")
            .body(template.render().unwrap())
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
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
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let post = find_post(repo, post_id.clone());
        let event = post.edit_post(
            FromStr::from_str(params.language.as_str()).unwrap(),
            params.title.to_owned(),
            params.markdown_content.to_owned(),
        );
        repo.save(event.clone());
        match event {
            PostEvent::PostEdited(_) => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/posts/{}", post.aggregate_id().clone()))
                .body(""),
            _ => HttpResponse::Found()
                .header(actix_web::http::header::LOCATION, format!("/admin/posts/{}", post_id.clone()))
                .body("")
        }
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

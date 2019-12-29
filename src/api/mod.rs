use std::convert::identity;
use std::str::FromStr;

use actix_web::{Error, HttpResponse, web};
use actix_web::web::{Json, Path};
use serde::Serialize;

use crate::api::requests::{EditPost, SubmitDraft};
use crate::api::resources::{DraftResource, PostResource};
use crate::pool::Pool;
use crate::post::Post;
use crate::post::PostEvent;
use crate::post::PostEvent::{DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostError, PostPublished};
use crate::post_repository::{PgPostRepository, PostRepository};

pub mod requests;
pub mod resources;

pub async fn list_drafts(pool: web::Data<Pool>) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let all_drafts: Vec<DraftResource> = repo.all_drafts()
            .iter()
            .map(DraftResource::from)
            .collect();
        return HttpResponse::Ok().json(all_drafts);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn list_posts(pool: web::Data<Pool>) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let all_posts: Vec<PostResource> = repo.all_posts()
            .iter()
            .map(PostResource::from)
            .collect();
        HttpResponse::Ok().json(all_posts)
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn show_draft(
    draft_id: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return uuid::Uuid::from_str(&*draft_id)
            .map_err(|err| bad_request(err.to_string()))
            .and_then(|id| repo.read(id)
                .ok_or(not_found("not found".to_string()))
            )
            .and_then(|post| {
                return match post {
                    Post::Draft { .. } => repo.read(post.aggregate_id())
                        .ok_or(not_found("not found".to_string()))
                        .map(|post| HttpResponse::Ok().json(DraftResource::from(&post))),
                    _ => Err(bad_request("not a draft".to_string())),
                };
            })
            .unwrap_or_else(identity);
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn submit_draft(
    params: web::Json<SubmitDraft>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        let draft = Post::NonExisting { aggregate_id: uuid::Uuid::new_v4() };
        return submit_or_edit_draft(params, repo, draft);
    })
        .unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

fn submit_or_edit_draft(
    params: Json<SubmitDraft>,
    repo: &mut PgPostRepository<'_>,
    draft: Post,
) -> HttpResponse {
    let event = draft.submit_draft(
        FromStr::from_str(params.language.as_str()).unwrap(),
        params.title.to_owned(),
        params.markdown_content.to_owned(),
    );

    repo.save(event.clone());

    what_the_fuck(repo, draft, event)
}

pub async fn make_draft_public(
    paths: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return get_post_from_params(paths, repo)
            .map(|post| {
                let event = post.make_public();

                repo.save(event.clone());

                what_the_fuck(repo, post, event)
            })
            .unwrap_or_else(identity);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn edit_draft(
    paths: web::Path<String>,
    params: web::Json<SubmitDraft>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return get_post_from_params(paths, repo)
            .map(|draft| { return submit_or_edit_draft(params, repo, draft); })
            .unwrap_or_else(identity);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn delete_draft(
    paths: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return get_post_from_params(paths, repo)
            .map(|post| {
                let event = post.delete_draft();

                repo.save(event.clone());

                what_the_fuck(repo, post, event)
            })
            .unwrap_or_else(identity);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn publish_draft(
    paths: web::Path<String>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return get_post_from_params(paths, repo)
            .map(|post| {
                let event = post.publish_draft(chrono::Utc::now());

                repo.save(event.clone());

                what_the_fuck(repo, post, event)
            })
            .unwrap_or_else(identity);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

pub async fn edit_post(
    paths: web::Path<String>,
    params: web::Json<EditPost>,
    pool: web::Data<Pool>,
) -> Result<HttpResponse, Error> {
    return Ok(PgPostRepository::from_pool(pool.get_ref(), |repo| {
        return get_post_from_params(paths, repo)
            .map(|post| {
                let event = post.edit_post(
                    FromStr::from_str(params.language.as_str()).unwrap(),
                    params.title.clone(),
                    params.markdown_content.clone(),
                );

                repo.save(event.clone());

                what_the_fuck(repo, post, event)
            }).unwrap_or_else(identity);
    }).unwrap_or_else(|err| HttpResponse::InternalServerError().json(err.to_string())));
}

fn what_the_fuck(repo: &mut PgPostRepository, post: Post, event: PostEvent) -> HttpResponse {
    match event {
        PostError(err) => bad_request(err.to_string()),
        DraftDeleted(_) => return_draft(repo, post),
        PostPublished(_) => return_post(repo, post),
        DraftSubmitted(_) => return_draft(repo, post),
        PostEdited(_) => return_post(repo, post),
        DraftMadePublic(_) => return_draft(repo, post),
    }
}

fn return_post(repo: &mut PgPostRepository, post: Post) -> HttpResponse {
    repo.read(post.aggregate_id())
        .map(|post| HttpResponse::Ok().json(PostResource::from(&post)))
        .unwrap_or(not_found("not found".to_string()))
}

fn return_draft(repo: &mut PgPostRepository, post: Post) -> HttpResponse {
    repo.read(post.aggregate_id())
        .map(|post| HttpResponse::Ok().json(DraftResource::from(&post)))
        .unwrap_or(not_found("not found".to_string()))
}

fn get_post_from_params(
    paths: Path<String>,
    repo: &mut PgPostRepository<'_>,
) -> Result<Post, HttpResponse> {
    uuid::Uuid::from_str(paths.as_str())
        .map_err(|err| bad_request(err.to_string()))
        .and_then(|id| repo.read(id)
            .ok_or(not_found("not found".to_string()))
        )
}

fn not_found<T: Serialize>(t: T) -> HttpResponse {
    HttpResponse::NotFound().json(t)
}

fn bad_request<T: Serialize>(t: T) -> HttpResponse {
    HttpResponse::BadRequest().json(t)
}


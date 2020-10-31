use std::rc::Rc;

use actix::{Actor, SyncContext};
use chrono::{DateTime, Utc};
use postgres::{Client, Row, Transaction};
use uuid::Uuid;

use crate::domain::post::{
    InnerArchivedDraft, InnerDraftDeleted, InnerDraftMadePublic, InnerDraftSubmitted,
    InnerPostEdited, InnerPostPublished, Post, PostEvent,
};
use crate::domain::repository::PostRepository;
use crate::domain::types::{Language, Markdown, PostId};
use crate::infra::pool::Pool;

pub struct TransactionalPostRepository<'a> {
    pub transaction: Transaction<'a>,
}

impl<'a> TransactionalPostRepository<'a> {
    fn submit_draft(&mut self, event: InnerDraftSubmitted) {
        self.transaction.execute(
            "insert into blog_posts (aggregate_id, status, language, title, markdown_content, version) \
            values ($1, $2, $3, $4, $5, $7) \
            on conflict (aggregate_id) do update \
            set language = $3, \
            title = $4, \
            markdown_content = $5, \
            version = $7\
            where blog_posts.version = $6",
            &[&event.post_id.to_uuid(), &"draft", &event.language.to_string(), &event.title, &event.markdown_content, &event.version, &(event.version + 1)],
        ).unwrap();
    }

    fn make_draft_public(&mut self, event: InnerDraftMadePublic) {
        self.transaction
            .execute(
                "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
                &[&event.post_id.to_uuid(), &event.post_id.to_str(), &true],
            )
            .unwrap();

        self.transaction.execute(
            "update blog_posts set slug = $1, version = $3 where aggregate_id = $1 and blog_posts.version = $2",
            &[&event.post_id.to_uuid(), &event.version, &(event.version + 1)],
        ).unwrap();
    }

    fn archive_draft(&mut self, event: InnerArchivedDraft) {
        self.transaction.execute(
            "update blog_posts set status = $1, version = $4 where aggregate_id = $2 and blog_posts.version = $3",
            &[&"archived", &event.post_id.to_uuid(), &event.version, &(event.version + 1)],
        ).unwrap();
    }

    fn delete_draft(&mut self, event: InnerDraftDeleted) {
        self.transaction
            .execute(
                "delete from blog_posts where aggregate_id = $1 and blog_posts.version = $2",
                &[&event.post_id.to_uuid(), &event.version],
            )
            .unwrap();
    }

    fn publish_post(&mut self, event: InnerPostPublished) {
        self.transaction
            .execute(
                "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
                &[&event.post_id.to_uuid(), &event.slug, &true],
            )
            .unwrap();
        self.transaction
            .execute(
                "update blog_posts \
            set status = $2, slug = $3, publication_date = $4, \
                version = $6 \
            where aggregate_id = $1 and blog_posts.version = $5",
                &[
                    &event.post_id.to_uuid(),
                    &"published",
                    &event.slug,
                    &event.publication_date,
                    &event.version,
                    &(event.version + 1),
                ],
            )
            .unwrap();
    }

    fn edit_post(&mut self, event: InnerPostEdited) {
        event
            .slug
            .clone()
            .map(|slug| {
                self.transaction
                    .execute(
                        "update blog_slugs set current = $2 where aggregate_id = $1",
                        &[&event.post_id.to_uuid(), &false],
                    )
                    .unwrap();
                self.transaction
                    .execute(
                        "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
                        &[&event.post_id.to_uuid(), &slug, &true],
                    )
                    .unwrap()
            })
            .unwrap_or(0);
        event
            .title
            .clone()
            .map(|title| {
                self.transaction
                    .execute(
                        "update blog_posts \
                set markdown_content = $2, language = $3, title = $4, version = $6 \
                where aggregate_id = $1 and blog_posts.version = $5",
                        &[
                            &event.post_id.to_uuid(),
                            &event.markdown_content,
                            &event.language.to_string(),
                            &title,
                            &event.version,
                            &(event.version + 1),
                        ],
                    )
                    .unwrap()
            })
            .unwrap_or_else(|| {
                self.transaction
                    .execute(
                        "update blog_posts \
                set markdown_content = $2, language = $3, version = $5 \
                where aggregate_id = $1 and blog_posts.version = $4",
                        &[
                            &event.post_id.to_uuid(),
                            &event.markdown_content,
                            &event.language.to_string(),
                            &event.version,
                            &(event.version + 1),
                        ],
                    )
                    .unwrap()
            });
    }
}

impl<'a> PostRepository for TransactionalPostRepository<'a> {
    fn all(&mut self) -> Vec<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    order by blog_posts.publication_date desc nulls first",
            &[],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_posts(&mut self) -> Vec<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1 \
                    order by blog_posts.publication_date desc",
            &[&"published"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_drafts(&mut self) -> Vec<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1",
            &[&"draft"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_archived(&mut self) -> Vec<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1",
            &[&"archived"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn find_by_slug(&mut self, slug: String) -> Option<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.aggregate_id = (
                        select blog_slugs.aggregate_id
                        from blog_slugs
                        where blog_slugs.slug = $1
                    )",
            &[&slug],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post()
    }

    fn read(&mut self, post_id: PostId) -> Option<Post> {
        self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.aggregate_id = $1",
            &[&post_id.to_uuid()],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post()
    }

    fn save(&mut self, event: PostEvent) {
        match event {
            PostEvent::DraftDeleted(e) => self.delete_draft(e),
            PostEvent::PostPublished(e) => self.publish_post(e),
            PostEvent::DraftSubmitted(e) => self.submit_draft(e),
            PostEvent::PostEdited(e) => self.edit_post(e),
            PostEvent::DraftMadePublic(e) => self.make_draft_public(e),
            PostEvent::ArchivedDraft(e) => self.archive_draft(e),
            PostEvent::PostError(_) => {}
        }
    }

    fn upsert(&mut self, post: Post) {
        match post {
            Post::NonExisting { post_id } => {
                self.transaction
                    .execute(
                        "delete from blog_posts where aggregate_id = $1",
                        &[&post_id.to_uuid()],
                    )
                    .unwrap();
            }
            Post::Draft {
                post_id,
                version,
                title,
                markdown_content,
                language,
                shareable,
                archived,
            } => {
                self.transaction.execute(
                    "insert into blog_posts (aggregate_id, status, language, title, markdown_content, version) \
                            values ($1, $2, $3, $4, $5, $6) \
                            on conflict (aggregate_id) do update \
                            set status = $2, \
                            language = $3, \
                            title = $4, \
                            markdown_content = $5, \
                            version = $6",
                    &[
                        &post_id.to_uuid(),
                        if archived { &"archived" } else { &"draft" },
                        &language.to_string(),
                        &title,
                        &markdown_content.to_edit(),
                        &version
                    ])
                    .unwrap();
                if shareable {
                    self.transaction.execute(
                        "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3) \
                                on conflict (aggregate_id, slug) do update \
                                set current = $3",
                        &[&post_id.to_uuid(), &post_id.to_str(), &true],
                    )
                        .unwrap();
                }
            }
            Post::Post {
                post_id,
                version,
                title,
                markdown_content,
                language,
                publication_date,
                current_slug,
                previous_slugs,
            } => {
                self.transaction.execute(
                    "insert into blog_posts (aggregate_id, status, language, title, markdown_content, publication_date, version) \
                            values ($1, $2, $3, $4, $5, $6, $7) \
                            on conflict (aggregate_id) do update \
                            set status = $2, \
                            language = $3, \
                            title = $4, \
                            markdown_content = $5, \
                            publication_date = $6, \
                            version = $7",
                    &[
                        &post_id.to_uuid(),
                        &"published",
                        &language.to_string(),
                        &title,
                        &markdown_content.to_edit(),
                        &publication_date,
                        &version
                    ])
                    .unwrap();
                self.transaction
                    .execute(
                        "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3) \
                                on conflict (aggregate_id, slug) do update \
                                set current = $3",
                        &[&post_id.to_uuid(), &current_slug.as_str(), &true],
                    )
                    .unwrap();
                for slug in previous_slugs {
                    self.transaction.execute(
                        "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3) \
                                on conflict (aggregate_id, slug) do update \
                                set current = $3",
                        &[&post_id.to_uuid(), &slug.as_str(), &false],
                    )
                        .unwrap();
                }
            }
        };
    }
}

pub struct ReadOnlyPostRepository<'a> {
    pub client: &'a mut Client,
}

impl<'a> PostRepository for ReadOnlyPostRepository<'a> {
    fn all(&mut self) -> Vec<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    order by blog_posts.publication_date desc nulls first",
            &[],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_posts(&mut self) -> Vec<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1 \
                    order by blog_posts.publication_date desc",
            &[&"published"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_drafts(&mut self) -> Vec<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1",
            &[&"draft"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn all_archived(&mut self) -> Vec<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1",
            &[&"archived"],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect()
    }

    fn find_by_slug(&mut self, slug: String) -> Option<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.aggregate_id = (
                        select blog_slugs.aggregate_id
                        from blog_slugs
                        where blog_slugs.slug = $1
                    )",
            &[&slug],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post()
    }

    fn read(&mut self, post_id: PostId) -> Option<Post> {
        self.client.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.aggregate_id = $1",
            &[&post_id.to_uuid()],
        )
            .unwrap().iter()
            .map(Rc::new)
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post()
    }

    fn save(&mut self, event: PostEvent) {
        panic!("Could not save {:?} outside a transaction", event);
    }

    fn upsert(&mut self, post: Post) {
        panic!("Could not save {:?} outside a transaction", post);
    }
}

pub struct PgActor(pub Pool);

impl Actor for PgActor {
    type Context = SyncContext<Self>;
}

#[derive(Clone)]
enum PostBuilder {
    Draft {
        post_id: uuid::Uuid,
        version: u32,
        title: String,
        markdown_content: String,
        language: Language,
        shareable: bool,
        archived: bool,
    },
    Post {
        post_id: uuid::Uuid,
        version: u32,
        title: String,
        markdown_content: String,
        language: Language,
        publication_date: DateTime<Utc>,
        current_slug: Option<String>,
        previous_slugs: Vec<String>,
        next_slug_is_current: bool,
    },
}

impl PostBuilder {
    fn post_builder_from_row(row: &Row) -> PostBuilder {
        let post_id = row.get(0);
        let status: String = row.get(1);
        let lang_string: String = row.get(2);
        let language = lang_string.parse().unwrap();
        let title = row.get(3);
        let maybe_content: Option<String> = row.get(4);
        let time: Option<DateTime<Utc>> = row.get(5);
        let slug: Option<String> = row.get(6);
        let current_slug: Option<bool> = row.get(7);
        let version: u32 = row.get(8);
        match &*status {
            "archived" => PostBuilder::Draft {
                post_id,
                version,
                language,
                title,
                markdown_content: maybe_content.unwrap_or_else(|| "".to_string()),
                shareable: slug.is_some(),
                archived: true,
            },
            "draft" => PostBuilder::Draft {
                post_id,
                version,
                language,
                title,
                markdown_content: maybe_content.unwrap_or_else(|| "".to_string()),
                shareable: slug.is_some(),
                archived: false,
            },
            "published" => PostBuilder::Post {
                post_id,
                version,
                language,
                title,
                markdown_content: maybe_content.unwrap_or_else(|| "".to_string()),
                publication_date: time.unwrap(),
                current_slug: if current_slug.unwrap() {
                    Some(slug.clone().unwrap())
                } else {
                    None
                },
                previous_slugs: if current_slug.unwrap() {
                    vec![]
                } else {
                    vec![slug.unwrap()]
                },
                next_slug_is_current: false,
            },
            _ => panic!("illegal post status : ".to_owned() + &*status),
        }
    }

    fn build(self) -> Post {
        match self {
            PostBuilder::Draft {
                post_id,
                version,
                title,
                markdown_content,
                language,
                shareable,
                archived,
            } => Post::Draft {
                post_id: PostId::new(post_id),
                version,
                title,
                markdown_content: Markdown::new(markdown_content),
                language,
                shareable,
                archived,
            },
            PostBuilder::Post {
                post_id,
                version,
                title,
                markdown_content,
                language,
                publication_date,
                current_slug,
                previous_slugs,
                ..
            } => Post::Post {
                post_id: PostId::new(post_id),
                version,
                title,
                markdown_content: Markdown::new(markdown_content),
                language,
                publication_date,
                current_slug: current_slug.expect("no current_slug found"),
                previous_slugs,
            },
        }
    }

    fn current_slug(self, current_slug: bool) -> PostBuilder {
        if current_slug {
            match self {
                PostBuilder::Draft { .. } => self,
                PostBuilder::Post {
                    post_id,
                    version,
                    title,
                    markdown_content,
                    language,
                    publication_date,
                    current_slug,
                    previous_slugs,
                    ..
                } => PostBuilder::Post {
                    post_id,
                    version,
                    title,
                    markdown_content,
                    language,
                    publication_date,
                    current_slug,
                    previous_slugs,
                    next_slug_is_current: true,
                },
            }
        } else {
            self
        }
    }

    fn with_slug(self, slug: String) -> PostBuilder {
        match self {
            PostBuilder::Draft {
                post_id,
                version,
                title,
                markdown_content,
                language,
                archived,
                ..
            } => PostBuilder::Draft {
                post_id,
                version,
                title,
                markdown_content,
                language,
                shareable: true,
                archived,
            },
            PostBuilder::Post {
                post_id,
                version,
                title,
                markdown_content,
                language,
                publication_date,
                current_slug,
                previous_slugs,
                next_slug_is_current,
            } => {
                if next_slug_is_current {
                    PostBuilder::Post {
                        post_id,
                        version,
                        title,
                        markdown_content,
                        language,
                        publication_date,
                        current_slug: Some(slug),
                        previous_slugs,
                        next_slug_is_current: false,
                    }
                } else {
                    let mut new_previous_slugs = previous_slugs;
                    new_previous_slugs.push(slug);
                    PostBuilder::Post {
                        post_id,
                        version,
                        title,
                        markdown_content,
                        language,
                        publication_date,
                        current_slug,
                        previous_slugs: new_previous_slugs,
                        next_slug_is_current,
                    }
                }
            }
        }
    }

    fn post_id(self) -> Uuid {
        match self {
            PostBuilder::Draft { post_id, .. } => post_id,
            PostBuilder::Post { post_id, .. } => post_id,
        }
    }
}

#[derive(Clone)]
struct RowsToPostsBuilder {
    head: Option<PostBuilder>,
    materialized_posts: Vec<Post>,
}

impl RowsToPostsBuilder {
    fn new() -> RowsToPostsBuilder {
        RowsToPostsBuilder {
            head: None,
            materialized_posts: vec![],
        }
    }

    fn fold_rows(self, row: Rc<&Row>) -> RowsToPostsBuilder {
        self.clone()
            .head
            .map(|existing| -> RowsToPostsBuilder {
                let post_id: Uuid = row.get(0);
                if post_id == existing.clone().post_id() {
                    let builder = existing.current_slug(row.get(7)).with_slug(row.get(6));
                    RowsToPostsBuilder {
                        head: Some(builder),
                        materialized_posts: self.clone().materialized_posts,
                    }
                } else {
                    let mut new_posts = self.clone().materialized_posts;
                    new_posts.push(existing.build());
                    RowsToPostsBuilder {
                        head: Some(PostBuilder::post_builder_from_row(&row)),
                        materialized_posts: new_posts,
                    }
                }
            })
            .unwrap_or_else(|| RowsToPostsBuilder {
                head: Some(PostBuilder::post_builder_from_row(&row)),
                materialized_posts: vec![],
            })
    }

    fn first_post(self) -> Option<Post> {
        self.head.map(PostBuilder::build)
    }

    fn collect(self) -> Vec<Post> {
        self.clone()
            .head
            .map(|builder| {
                let mut results = self.clone().materialized_posts;
                results.push(builder.build());
                results
            })
            .unwrap_or(self.materialized_posts)
    }
}

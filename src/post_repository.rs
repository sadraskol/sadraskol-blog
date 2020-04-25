use std::rc::Rc;

use actix::{Actor, SyncContext};
use chrono::{DateTime, Utc};
use postgres::{Row, Transaction};
use uuid::Uuid;

use crate::pool::Pool;
use crate::post::{PostId, InnerDraftDeleted, InnerDraftMadePublic, InnerDraftSubmitted, InnerPostEdited, InnerPostPublished, Language, Markdown, Post, PostEvent};

pub trait PostRepository {
    fn all(&mut self) -> Vec<Post>;
    fn all_posts(&mut self) -> Vec<Post>;
    fn all_drafts(&mut self) -> Vec<Post>;
    fn find_by_slug(&mut self, slug: String) -> Option<Post>;
    fn read(&mut self, post_id: PostId) -> Option<Post>;
    fn save(&mut self, event: PostEvent);
}

pub struct PgPostRepository<'a> {
    pub transaction: Transaction<'a>,
}

impl<'a> PgPostRepository<'a> {
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
        self.transaction.execute(
            "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
            &[
                &event.post_id.to_uuid(),
                &event.post_id.to_str(),
                &true
            ],
        ).unwrap();

        self.transaction.execute(
            "update blog_posts set slug = $1, version = $3 where aggregate_id = $1 and blog_posts.version = $2",
            &[&event.post_id.to_uuid(), &event.version, &(event.version + 1)],
        ).unwrap();
    }

    fn delete_draft(&mut self, event: InnerDraftDeleted) {
        self.transaction.execute(
            "delete from blog_posts where aggregate_id = $1 and blog_posts.version = $2",
            &[&event.post_id.to_uuid(), &event.version],
        ).unwrap();
    }

    fn publish_post(&mut self, event: InnerPostPublished) {
        self.transaction.execute(
            "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
            &[&event.post_id.to_uuid(), &event.slug, &true],
        ).unwrap();
        self.transaction.execute(
            "update blog_posts \
            set status = $2, slug = $3, publication_date = $4, \
                version = $6 \
            where aggregate_id = $1 and blog_posts.version = $5",
            &[&event.post_id.to_uuid(), &"published", &event.slug, &event.publication_date, &event.version, &(event.version + 1)],
        ).unwrap();
    }

    fn edit_post(&mut self, event: InnerPostEdited) {
        event.slug.clone().map(|slug| {
            self.transaction.execute(
                "update blog_slugs set current = $2 where aggregate_id = $1",
                &[&event.post_id.to_uuid(), &false],
            ).unwrap();
            self.transaction.execute(
                "insert into blog_slugs(aggregate_id, slug, current) values($1, $2, $3)",
                &[&event.post_id.to_uuid(), &slug, &true],
            ).unwrap()
        }).unwrap_or(0);
        event.title.clone().map(|title|
            self.transaction.execute(
                "update blog_posts \
                set markdown_content = $2, language = $3, title = $4, version = $6 \
                where aggregate_id = $1 and blog_posts.version = $5",
                &[
                    &event.post_id.to_uuid(),
                    &event.markdown_content,
                    &event.language.to_string(),
                    &title,
                    &event.version,
                    &(event.version + 1)
                ],
            ).unwrap()
        ).unwrap_or_else(|| {
            self.transaction.execute(
                "update blog_posts \
                set markdown_content = $2, language = $3, version = $5 \
                where aggregate_id = $1 and blog_posts.version = $4",
                &[
                    &event.post_id.to_uuid(),
                    &event.markdown_content,
                    &event.language.to_string(),
                    &event.version,
                    &(event.version + 1)
                ],
            ).unwrap()
        });
    }
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
        return match &*status {
            "draft" => PostBuilder::Draft {
                post_id,
                version,
                language,
                title,
                markdown_content: maybe_content.unwrap_or("".to_string()),
                shareable: slug.is_some(),
            },
            "published" => PostBuilder::Post {
                post_id,
                version,
                language,
                title,
                markdown_content: maybe_content.unwrap_or("".to_string()),
                publication_date: time.unwrap(),
                current_slug: if current_slug.unwrap() { Some(slug.clone().unwrap()) } else { None },
                previous_slugs: if current_slug.unwrap() { vec![] } else { vec![slug.clone().unwrap()] },
                next_slug_is_current: false,
            },
            _ => panic!("illegal post status : ".to_owned() + &*status),
        };
    }

    fn build(self) -> Post {
        match self {
            PostBuilder::Draft { post_id, version, title, markdown_content, language, shareable } =>
                Post::Draft { post_id: PostId::new(post_id), version, title, markdown_content: Markdown::new(markdown_content), language, shareable },
            PostBuilder::Post { post_id, version, title, markdown_content, language, publication_date, current_slug, previous_slugs, .. } =>
                Post::Post { post_id: PostId::new(post_id), version, title, markdown_content: Markdown::new(markdown_content), language, publication_date, current_slug: current_slug.expect("no current_slug found"), previous_slugs }
        }
    }

    fn current_slug(self, current_slug: bool) -> PostBuilder {
        if current_slug {
            match self {
                PostBuilder::Draft { .. } => self,
                PostBuilder::Post { post_id, version, title, markdown_content, language, publication_date, current_slug, previous_slugs, .. } =>
                    PostBuilder::Post { post_id, version, title, markdown_content, language, publication_date, current_slug, previous_slugs, next_slug_is_current: true }
            }
        } else {
            self
        }
    }

    fn with_slug(self, slug: String) -> PostBuilder {
        match self {
            PostBuilder::Draft { post_id, version, title, markdown_content, language, .. } =>
                PostBuilder::Draft { post_id, version, title, markdown_content, language, shareable: true },
            PostBuilder::Post { post_id, version, title, markdown_content, language, publication_date, current_slug, previous_slugs, next_slug_is_current } =>
                if next_slug_is_current {
                    PostBuilder::Post {
                        post_id,
                        version,
                        title,
                        markdown_content,
                        language,
                        publication_date,
                        current_slug: Some(slug.clone()),
                        previous_slugs,
                        next_slug_is_current: false,
                    }
                } else {
                    let mut new_previous_slugs = previous_slugs.clone();
                    new_previous_slugs.push(slug.clone());
                    PostBuilder::Post {
                        post_id,
                        version,
                        title,
                        markdown_content,
                        language,
                        publication_date,
                        current_slug,
                        previous_slugs: new_previous_slugs.clone(),
                        next_slug_is_current,
                    }
                }
        }
    }

    fn post_id(self) -> Uuid {
        return match self {
            PostBuilder::Draft { post_id, .. } => post_id,
            PostBuilder::Post { post_id, .. } => post_id,
        };
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
        return self.clone().head
            .map(|existing| -> RowsToPostsBuilder {
                let post_id: Uuid = row.get(0);
                if post_id == existing.clone().post_id() {
                    let builder = existing
                        .current_slug(row.get(7))
                        .with_slug(row.get(6));
                    RowsToPostsBuilder {
                        head: Some(builder),
                        materialized_posts: self.clone().materialized_posts,
                    }
                } else {
                    let mut new_posts = self.clone().materialized_posts;
                    new_posts.push(existing.build());
                    RowsToPostsBuilder {
                        head: Some(PostBuilder::post_builder_from_row(&row)),
                        materialized_posts: new_posts.clone(),
                    }
                }
            })
            .unwrap_or_else(|| {
                RowsToPostsBuilder {
                    head: Some(PostBuilder::post_builder_from_row(&row)),
                    materialized_posts: vec![],
                }
            });
    }

    fn first_post(self) -> Option<Post> {
        self.clone().head
            .map(PostBuilder::build)
    }

    fn collect(self) -> Vec<Post> {
        self.clone().head
            .map(|builder| {
                let mut results = self.clone().materialized_posts;
                results.push(builder.build());
                results
            })
            .unwrap_or(self.clone().materialized_posts)
    }
}

impl<'a> PostRepository for PgPostRepository<'a> {
    fn all(&mut self) -> Vec<Post> {
        return self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    order by blog_posts.publication_date desc nulls first",
            &[],
        )
            .unwrap().iter()
            .map(|row| Rc::new(row))
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect();
    }

    fn all_posts(&mut self) -> Vec<Post> {
        return self.transaction.query(
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
            .map(|row| Rc::new(row))
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect();
    }

    fn all_drafts(&mut self) -> Vec<Post> {
        return self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.status = $1",
            &[&"draft"],
        )
            .unwrap().iter()
            .map(|row| Rc::new(row))
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .collect();
    }

    fn find_by_slug(&mut self, slug: String) -> Option<Post> {
        return self.transaction.query(
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
            .map(|row| Rc::new(row))
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post();
    }

    fn read(&mut self, post_id: PostId) -> Option<Post> {
        return self.transaction.query(
            "select blog_posts.aggregate_id, blog_posts.status, blog_posts.language,
                           blog_posts.title, blog_posts.markdown_content, blog_posts.publication_date,
                           blog_slugs.slug, blog_slugs.current, blog_posts.version
                    from blog_posts
                    left outer join blog_slugs on blog_posts.aggregate_id = blog_slugs.aggregate_id
                    where blog_posts.aggregate_id = $1",
            &[&post_id.to_uuid()],
        )
            .unwrap().iter()
            .map(|row| Rc::new(row))
            .fold(RowsToPostsBuilder::new(), RowsToPostsBuilder::fold_rows)
            .first_post();
    }

    fn save(&mut self, event: PostEvent) {
        match event {
            PostEvent::DraftDeleted(e) => self.delete_draft(e),
            PostEvent::PostPublished(e) => self.publish_post(e),
            PostEvent::DraftSubmitted(e) => self.submit_draft(e),
            PostEvent::PostEdited(e) => self.edit_post(e),
            PostEvent::DraftMadePublic(e) => self.make_draft_public(e),
            PostEvent::PostError(_) => {}
        }
    }
}

pub struct DbExecutor(pub Pool);

impl Actor for DbExecutor {
    type Context = SyncContext<Self>;
}
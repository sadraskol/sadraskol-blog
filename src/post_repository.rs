use chrono::{DateTime, Utc};
use postgres::Connection;
use postgres::rows::Row;

use crate::post::{AggregateId, DraftDeleted, DraftMadePublic, DraftSubmitted, Post, PostEdited, PostPublished, Slug};

pub trait PostRepository {
    fn find(&self) -> Vec<Post>;
    fn all_drafts(&self) -> Vec<Post>;
    fn read(&self, aggregate_id: AggregateId) -> Post;
    fn submit_draft(&mut self, event: DraftSubmitted);
    fn make_draft_public(&mut self, event: DraftMadePublic);
    fn delete_draft(&mut self, event: DraftDeleted);
    fn publish_post(&mut self, event: PostPublished);
    fn edit_post(&mut self, event: PostEdited);
}

pub struct PgPostRepository<'a> {
    connection: &'a Connection
}

impl<'a> PgPostRepository<'a> {
    pub fn new(connection: &Connection) -> PgPostRepository {
        return PgPostRepository { connection };
    }
}

fn map_row_to_post(row: Row) -> Post {
    let status: String = row.get(1);
    let maybe_slug: Option<String> = row.get(6);
    let lang_string: String = row.get(2);
    let language = lang_string.parse().unwrap();
    let maybe_content: Option<String> = row.get(5);
    let time: Option<DateTime<Utc>> = row.get(7);
    return match &*status {
        "draft" => Post::Draft {
            aggregate_id: row.get(0),
            language,
            title: row.get(3),
            description: row.get(4),
            markdown_content: maybe_content.unwrap_or("".to_string()),
            shareable: maybe_slug.is_some(),
        },
        "published" => Post::Post {
            aggregate_id: row.get(0),
            language,
            title: row.get(3),
            description: row.get(4),
            markdown_content: maybe_content.unwrap_or("".to_string()),
            publication_date: time.unwrap(),
            current_slug: Slug { slug: maybe_slug.unwrap() },
            alternative_slugs: vec![],
        },
        _ => panic!("illegal post status : ".to_owned() + &*status),
    };
}


impl<'a> PostRepository for PgPostRepository<'a> {
    fn find(&self) -> Vec<Post> {
        return self.connection.query(
            "select aggregate_id, status, language, title, description, markdown_content, slug, publication_date \
                from blog_posts \
                where status = $1 \
                order by publication_date desc",
            &[&"published"],
        )
            .unwrap().iter()
            .map(map_row_to_post)
            .collect();
    }

    fn all_drafts(&self) -> Vec<Post> {
        return self.connection.query(
            "select aggregate_id, status, language, title, description, markdown_content, slug, publication_date \
                from blog_posts \
                where status = $1 \
                order by publication_date desc",
            &[&"draft"],
        )
            .unwrap().iter()
            .map(map_row_to_post)
            .collect();
    }

    fn read(&self, aggregate_id: AggregateId) -> Post {
        return self.connection.query(
            "select aggregate_id, status, language, title, description, markdown_content, slug, publication_date \
                from blog_posts \
                where aggregate_id = $1", &[&aggregate_id]).unwrap()
            .iter()
            .next()
            .map(map_row_to_post)
            .unwrap_or(Post::NonExisting { aggregate_id });
    }

    fn submit_draft(&mut self, event: DraftSubmitted) {
        self.connection.execute(
            "insert into blog_posts (aggregate_id, status, language, title, description, markdown_content) \
            values ($1, $2, $3, $4, $5, $6) \
            on conflict (aggregate_id) do update \
            set language = $3 \
            , title = $4 \
            , description = $5 \
            , markdown_content = $6",
            &[&event.aggregate_id, &"draft", &event.language.to_string(), &event.title, &event.description, &event.markdown_content],
        ).unwrap();
    }

    fn make_draft_public(&mut self, event: DraftMadePublic) {
        self.connection.execute(
            "update blog_posts set slug = $1 where aggregate_id = $1",
            &[&event.aggregate_id],
        ).unwrap();
    }

    fn delete_draft(&mut self, event: DraftDeleted) {
        self.connection.execute(
            "delete blog_posts where aggregate_id = $1",
            &[&event.aggregate_id],
        ).unwrap();
    }

    fn publish_post(&mut self, event: PostPublished) {
        self.connection.execute(
            "update blog_posts \
            set status = $2 \
            , slug = $3 \
            , publication_date = $4 \
            where aggregate_id = $1",
            &[&event.aggregate_id, &"published", &event.slug.slug, &event.publication_date],
        ).unwrap();
    }

    fn edit_post(&mut self, event: PostEdited) {
        self.connection.execute(
            "update blog_posts \
            set description = $2 \
            , markdown_content = $3 \
            , language = $4 \
            where aggregate_id = $1",
            &[
                &event.aggregate_id,
                &event.description,
                &event.markdown_content,
                &event.language.to_string()
            ],
        ).unwrap();
        event.title.clone().map(|title|
            self.connection.execute(
                "update blog_posts \
                set title = $2 \
                where aggregate_id = $1",
                &[&event.aggregate_id, &title],
            ).unwrap()
        ).unwrap_or(0);
    }
}

#[cfg(test)]
mod test {
    use crate::post::{AggregateId, DraftDeleted, DraftMadePublic, DraftSubmitted, Post, PostEdited, PostPublished};
    use crate::post::Post::NonExisting;
    use crate::post_repository::{PostRepository};

    struct MemoryPostRepository {
        data: Vec<Post>
    }

    impl PostRepository for MemoryPostRepository {
        fn find(&self) -> Vec<Post> {
            return self.data.clone();
        }

        fn all_drafts(&self) -> Vec<Post> {
            return self.data.iter()
                .filter(|post| return match post {
                    Post::NonExisting { .. } => false,
                    Post::Draft { .. } => true,
                    Post::Post { .. } => false,
                })
                .collect();
        }

        fn read(&self, aggregate_id: AggregateId) -> Post {
            return self.data.iter()
                .find(|post| post.aggregate_id() == aggregate_id)
                .map(|post| post.clone())
                .unwrap_or(NonExisting { aggregate_id: aggregate_id.clone() });
        }

        fn submit_draft(&mut self, event: DraftSubmitted) {
            let maybe_post = self.data.iter()
                .find(|post| post.aggregate_id() == event.aggregate_id);
            match maybe_post {
                None => self.data.push(Post::Draft {
                    aggregate_id: event.aggregate_id.clone(),
                    title: event.title.clone(),
                    description: event.description.clone(),
                    markdown_content: event.markdown_content.clone(),
                    language: event.language.clone(),
                    shareable: false,
                }),
                Some(post) => self.data = self.data
                    .iter()
                    .map(|post| if post.aggregate_id() == event.aggregate_id {
                        return match post {
                            Post::NonExisting { .. } => panic!("unexpected state"),
                            Post::Draft { title, description, markdown_content, language, shareable, .. } =>
                                Post::Draft {
                                    aggregate_id: event.aggregate_id.clone(),
                                    title: event.title.clone(),
                                    description: event.description.clone(),
                                    markdown_content: event.markdown_content.clone(),
                                    language: event.language.clone(),
                                    shareable: *shareable,
                                },
                            Post::Post { title, .. } => panic!("unexpected state"),
                        };
                    } else {
                        post.clone()
                    })
                    .collect()
            }
        }

        fn make_draft_public(&mut self, event: DraftMadePublic) {
            self.data = self.data
                .iter()
                .map(|post| if post.aggregate_id() == event.aggregate_id {
                    return match post {
                        Post::NonExisting { .. } => panic!("unexpected state"),
                        Post::Draft { title, description, markdown_content, language, .. } =>
                            Post::Draft {
                                aggregate_id: post.aggregate_id(),
                                title: title.clone(),
                                description: description.clone(),
                                markdown_content: markdown_content.clone(),
                                language: language.clone(),
                                shareable: true,
                            },
                        Post::Post { title, .. } => panic!("unexpected state"),
                    };
                } else {
                    post.clone()
                })
                .collect();
        }

        fn delete_draft(&mut self, event: DraftDeleted) {
            self.data = self.data
                .iter()
                .filter(|post| post.aggregate_id() != event.aggregate_id)
                .map(|post| post.clone())
                .collect();
        }

        fn publish_post(&mut self, event: PostPublished) {
            self.data = self.data
                .iter()
                .map(|post| if post.aggregate_id() == event.aggregate_id {
                    return match post {
                        Post::NonExisting { .. } => panic!("unexpected state"),
                        Post::Draft { title, description, markdown_content, language, .. } =>
                            Post::Post {
                                aggregate_id: post.aggregate_id(),
                                title: title.clone(),
                                description: description.clone(),
                                markdown_content: markdown_content.clone(),
                                language: language.clone(),
                                publication_date: event.publication_date.clone(),
                                current_slug: event.slug.clone(),
                                alternative_slugs: Vec::new(),
                            },
                        Post::Post { title, .. } => panic!("unexpected state"),
                    };
                } else {
                    post.clone()
                })
                .collect();
        }

        fn edit_post(&mut self, event: PostEdited) {
            self.data = self.data
                .iter()
                .map(|post| if post.aggregate_id() == event.aggregate_id {
                    return match post {
                        Post::NonExisting { .. } => panic!("unexpected state"),
                        Post::Draft { .. } => panic!("unexpected state"),
                        Post::Post { title, publication_date, current_slug, alternative_slugs, .. } =>
                            Post::Post {
                                aggregate_id: post.aggregate_id(),
                                title: event.title.clone().unwrap_or(title.clone()),
                                description: event.description.clone(),
                                markdown_content: event.markdown_content.clone(),
                                language: event.language.clone(),
                                publication_date: publication_date.clone(),
                                current_slug: current_slug.clone(),
                                alternative_slugs: alternative_slugs.clone(),
                            },
                    };
                } else {
                    post.clone()
                })
                .collect();
        }
    }
}
use actix::prelude::*;

use crate::domain::post::Post;
use crate::domain::repository::PostRepository;
use crate::domain::types::PostId;
use crate::infra::post_repository::{PgActor, ReadOnlyPostRepository};
use std::ops::DerefMut;

enum FindCriteria {
    POSTS,
    DRAFTS,
    ALL,
}

pub struct Find(FindCriteria);

impl Find {
    pub fn all() -> Find { Find(FindCriteria::ALL) }
    pub fn drafts() -> Find { Find(FindCriteria::DRAFTS) }
    pub fn posts() -> Find { Find(FindCriteria::POSTS) }
}

impl Message for Find {
    type Result = Result<Vec<Post>, String>;
}

impl Handler<Find> for PgActor {
    type Result = Result<Vec<Post>, String>;

    fn handle(&mut self, f: Find, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| { "pool empty".to_string() })?;
        let mut repository = ReadOnlyPostRepository { client: connection.deref_mut() };

        let vec = match f.0 {
            FindCriteria::POSTS => repository.all_posts(),
            FindCriteria::DRAFTS => repository.all_drafts(),
            FindCriteria::ALL => repository.all()
        };

        Ok(vec)
    }
}

enum FindByCriteria {
    SLUG(String),
    ID(PostId),
}

pub struct FindBy(FindByCriteria);

impl FindBy {
    pub fn slug(slug: String) -> FindBy { FindBy(FindByCriteria::SLUG(slug)) }
    pub fn id(id: PostId) -> FindBy { FindBy(FindByCriteria::ID(id)) }
}

impl Message for FindBy {
    type Result = Result<Option<Post>, String>;
}

impl Handler<FindBy> for PgActor {
    type Result = Result<Option<Post>, String>;

    fn handle(&mut self, f: FindBy, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| { "pool empty".to_string() })?;
        let mut repository = ReadOnlyPostRepository { client: connection.deref_mut() };

        let opt = match f.0 {
            FindByCriteria::SLUG(slug) => repository.find_by_slug(slug),
            FindByCriteria::ID(id) => repository.read(id),
        };

        Ok(opt)
    }
}
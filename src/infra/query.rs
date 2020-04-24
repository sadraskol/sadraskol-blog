use actix::prelude::*;

use crate::post::{AggregateId, Post};
use crate::post_repository::{DbExecutor, PgPostRepository, PostRepository};

enum FindCriteria {
    POSTS,
    DRAFTS,
    ALL
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

impl Handler<Find> for DbExecutor {
    type Result = Result<Vec<Post>, String>;

    fn handle(&mut self, f: Find, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| { "pool empty".to_string() })?;
        let transaction = connection.transaction().map_err(|_| { "no transaction?".to_string() })?;
        let mut repository = PgPostRepository { transaction };

        let vec = match f.0 {
            FindCriteria::POSTS => repository.all_posts(),
            FindCriteria::DRAFTS => repository.all_drafts(),
            FindCriteria::ALL => repository.all()
        };

        repository.transaction.commit().map_err(|_| { "commit failed".to_string() })?;
        Ok(vec)
    }
}

enum FindByCriteria {
    SLUG(String),
    ID(AggregateId),
}

pub struct FindBy(FindByCriteria);

impl FindBy {
    pub fn slug(slug: String) -> FindBy { FindBy(FindByCriteria::SLUG(slug)) }
    pub fn id(id: AggregateId) -> FindBy { FindBy(FindByCriteria::ID(id)) }
}

impl Message for FindBy {
    type Result = Result<Option<Post>, String>;
}

impl Handler<FindBy> for DbExecutor {
    type Result = Result<Option<Post>, String>;

    fn handle(&mut self, f: FindBy, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| { "pool empty".to_string() })?;
        let transaction = connection.transaction().map_err(|_| { "no transaction?".to_string() })?;
        let mut repository = PgPostRepository { transaction };

        let opt = match f.0 {
            FindByCriteria::SLUG(slug) => repository.find_by_slug(slug),
            FindByCriteria::ID(id) => repository.read(id),
        };

        repository.transaction.commit().map_err(|_| { "commit failed".to_string() })?;
        Ok(opt)
    }
}
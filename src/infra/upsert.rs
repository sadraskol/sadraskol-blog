use actix::prelude::*;

use crate::domain::post::Post;
use crate::domain::repository::PostRepository;
use crate::infra::post_repository::{PgActor, TransactionalPostRepository};

#[derive(Clone)]
pub struct UpsertCommand(pub Post);

impl Message for UpsertCommand {
    type Result = Result<(), String>;
}

impl Handler<UpsertCommand> for PgActor {
    type Result = Result<(), String>;

    fn handle(&mut self, command: UpsertCommand, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| "pool empty".to_string())?;
        let transaction = connection
            .transaction()
            .map_err(|_| "no transaction?".to_string())?;
        let mut repository = TransactionalPostRepository { transaction };

        log::info!("upserting command {:?}", command.0.post_id().to_str());
        repository.upsert(command.0);

        repository
            .transaction
            .commit()
            .map_err(|_| "commit failed".to_string())?;
        Ok(())
    }
}

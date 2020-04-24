use actix::prelude::*;
use chrono::{DateTime, Utc};

use crate::post::{AggregateId, Language, Post, PostEvent};
use crate::post_repository::{DbExecutor, PgPostRepository, PostRepository};

type Title = String;
type Content = String;

pub enum Command {
    SubmitDraft(AggregateId, Language, Title, Content),
    MakePublic(AggregateId),
    DeleteDraft(AggregateId),
    PublishDraft(AggregateId, DateTime<Utc>),
    EditPost(AggregateId, Language, Title, Content),
}

impl Command {
    fn id(&self) -> AggregateId {
        match self {
            Command::SubmitDraft(id, _, _, _) => *id,
            Command::MakePublic(id) => *id,
            Command::DeleteDraft(id) => *id,
            Command::PublishDraft(id, _) => *id,
            Command::EditPost(id, _, _, _) => *id,
        }
    }
}

impl Message for Command {
    type Result = Result<PostEvent, String>;
}

impl Handler<Command> for DbExecutor {
    type Result = Result<PostEvent, String>;

    fn handle(&mut self, command: Command, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().map_err(|_| { "pool empty".to_string() })?;
        let transaction = connection.transaction().map_err(|_| { "no transaction?".to_string() })?;
        let mut repository = PgPostRepository { transaction };

        let post = get_post(&mut repository, command.id());
        let e = match command {
            Command::SubmitDraft(_, lang, title, content) =>
                post.submit_draft(lang, title, content),
            Command::MakePublic(_) =>
                post.make_public(),
            Command::DeleteDraft(_) =>
                post.delete_draft(),
            Command::PublishDraft(_, datetime) =>
                post.publish_draft(datetime),
            Command::EditPost(_, lang, title, content) =>
                post.edit_post(lang, title, content),
        };
        repository.save(e.clone());

        repository.transaction.commit().map_err(|_| { "commit failed".to_string() })?;
        Ok(e)
    }
}

fn get_post(repository: &mut PgPostRepository, id: AggregateId) -> Post {
    let draft = repository.read(id).unwrap_or(Post::NonExisting { aggregate_id: id });
    draft
}

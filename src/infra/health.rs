use actix::{Handler, Message};

use crate::post_repository::DbExecutor;
use postgres::Error;

pub struct Health;

impl Health {
    pub fn new() -> Health { Health {} }
}

impl Message for Health {
    type Result = Result<(), Error>;
}

impl Handler<Health> for DbExecutor {
    type Result = Result<(), Error>;

    fn handle(&mut self, _: Health, _: &mut Self::Context) -> Self::Result {
        let mut connection = self.0.get().unwrap();
        connection.query("values (1)", &[])?;
        Ok(())
    }
}
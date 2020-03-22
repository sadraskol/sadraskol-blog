use postgres::{Client, Error, NoTls};
use r2d2::ManageConnection;

use crate::config::Postgres;

#[derive(Debug, Clone)]
pub struct ConnectionManager {
    postgres: Postgres
}

impl ConnectionManager {
    pub fn new(config: Postgres) -> Self {
        ConnectionManager { postgres: config }
    }
}

impl ManageConnection for ConnectionManager {
    type Connection = Client;
    type Error = Error;

    fn connect(&self) -> Result<Client, Error> {
        Client::connect(self.postgres.url.as_str(), NoTls)
    }

    fn is_valid(&self, conn: &mut Client) -> Result<(), Error> {
        conn.execute("values(1)", &[])
            .map(|_| ())
    }

    fn has_broken(&self, conn: &mut Client) -> bool {
        conn.is_closed()
    }
}

pub type Pool = r2d2::Pool<ConnectionManager>;
use postgres::{Connection, Error, TlsMode};
use r2d2::ManageConnection;

#[derive(Debug, Clone)]
pub struct ConnectionManager {
    database_url: String
}

impl ConnectionManager {
    pub fn new<S: Into<String>>(database_url: S) -> Self {
        ConnectionManager {
            database_url: database_url.into()
        }
    }
}

impl ManageConnection for ConnectionManager {
    type Connection = Connection;
    type Error = Error;

    fn connect(&self) -> Result<Connection, Error> {
        Connection::connect(self.database_url.as_str(), TlsMode::None)
    }

    fn is_valid(&self, conn: &mut Connection) -> Result<(), Error> {
        conn.execute("SELECT 1", &[])
            .map(|_| ())
    }

    fn has_broken(&self, _conn: &mut Connection) -> bool {
        false
    }
}

pub type Pool = r2d2::Pool<ConnectionManager>;
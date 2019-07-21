use openssl::ssl::{SslConnector, SslFiletype, SslMethod};
use postgres::{Client, Error, NoTls};
use postgres_openssl::MakeTlsConnector;
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
        self.postgres.ssl.clone()
            .map(|ssl| {
                let mut builder = SslConnector::builder(SslMethod::tls()).unwrap();
                builder.set_ca_file(std::path::PathBuf::from(ssl.ca_path)).unwrap();
                builder.set_certificate_chain_file(std::path::PathBuf::from(ssl.cert_path)).unwrap();
                builder.set_private_key_file(std::path::PathBuf::from(ssl.key_path), SslFiletype::PEM).unwrap();
                let connector = MakeTlsConnector::new(builder.build());

                Client::connect(
                    self.postgres.url.as_str(),
                    connector,
                )
            })
            .unwrap_or(Client::connect(
                self.postgres.url.as_str(),
                NoTls,
            ))
    }

    fn is_valid(&self, conn: &mut Client) -> Result<(), Error> {
        conn.execute("values(1)", &[])
            .map(|_| ())
    }

    fn has_broken(&self, _conn: &mut Client) -> bool {
        false
    }
}

pub type Pool = r2d2::Pool<ConnectionManager>;
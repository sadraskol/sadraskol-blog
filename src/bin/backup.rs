extern crate actix_web;
extern crate sadraskol;

use std::time::Duration;

use actix::SyncArbiter;

use sadraskol::config;
use sadraskol::domain::post::ExportedPost;
use sadraskol::infra::pool;
use sadraskol::infra::post_repository::PgActor;
use sadraskol::infra::upsert::UpsertCommand;

#[actix_rt::main]
async fn main() -> std::io::Result<()> {
    std::env::set_var("RUST_LOG", "info");
    env_logger::init();

    let config = config::cfg();
    let pool = r2d2::Pool::builder()
        .connection_timeout(Duration::from_secs(4))
        .build(pool::ConnectionManager::new(config.postgres))
        .expect("Failed to create pool");

    let addr = SyncArbiter::start(1, move || PgActor(pool.clone()));

    let exported_as_str = std::fs::read_to_string("./backup.json").unwrap();
    let exported_posts: Vec<ExportedPost> = serde_json::from_str(&exported_as_str).unwrap();

    let commands: Vec<UpsertCommand> = exported_posts
        .iter()
        .filter_map(|post| post.import_post())
        .map(UpsertCommand)
        .collect();

    for c in commands {
        addr.send(c.clone())
            .await
            .unwrap_or_else(|_| panic!("sending {:?} to actor failed", c.0.post_id().to_str()))
            .unwrap();
    }

    Ok(())
}

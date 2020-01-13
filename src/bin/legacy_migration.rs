extern crate sadraskol;

use std::fs;
use std::path::PathBuf;

use postgres::{Client, NoTls};

fn main() {
    let sql_file = std::env::var("SQL_FILE").unwrap_or("./sadraskol.sql".to_string());
    let config = sadraskol::config::cfg();
    let mut connection = Client::connect(config.postgres.url.as_str(), NoTls).unwrap();
    let contents = fs::read_to_string(PathBuf::from(sql_file)).unwrap();
    let mut transaction = connection.transaction().unwrap();
    transaction.batch_execute(contents.as_str()).unwrap();
    transaction.batch_execute("\
        insert into blog_posts (aggregate_id, status, language, title, markdown_content, publication_date) \
        select cast(aggregate_id as uuid), status, language, title, markdown_content, pub_date from blog_post_projections;
        insert into blog_slugs (aggregate_id, slug, current) \
        select cast(aggregate_id as uuid), slug, slug = redirection from blog_slug_projections;"
    ).unwrap();
    transaction.commit().unwrap();
}
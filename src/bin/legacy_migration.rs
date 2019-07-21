extern crate sadraskol;

use std::fs;
use std::path::PathBuf;

use postgres::{Client, NoTls};

fn main() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("sadraskol.sql");
    let mut connection = Client::connect("postgres://postgres:postgres@localhost:5433/sadraskol_dev", NoTls).unwrap();
    let contents = fs::read_to_string(d).unwrap();
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
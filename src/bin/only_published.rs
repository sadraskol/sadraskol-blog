extern crate actix_web;
extern crate sadraskol;

use sadraskol::domain::post::ExportedPost;

#[actix_rt::main]
async fn main() -> std::io::Result<()> {
    std::env::set_var("RUST_LOG", "info");
    env_logger::init();

    let exported_as_str = std::fs::read_to_string("./backup.json").unwrap();
    let exported_posts: Vec<ExportedPost> = serde_json::from_str(&exported_as_str).unwrap();

    let mut published_posts: Vec<ExportedPost> = vec![];
    for p in exported_posts {
        if p.publication_date.is_some() {
            published_posts.push(p);
        }
    }

    let published_as_str = serde_json::to_string(&published_posts).unwrap();
    std::fs::write("./clean-backup.json", published_as_str).unwrap();

    Ok(())
}
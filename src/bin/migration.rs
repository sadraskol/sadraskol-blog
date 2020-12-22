extern crate sadraskol;

use std::borrow::BorrowMut;
use std::fs;

use postgres::{Client, NoTls};

use sadraskol::config;
use sadraskol::domain::post::Post;
use sadraskol::domain::repository::PostRepository;
use sadraskol::infra::post_repository::ReadOnlyPostRepository;
use std::io::Write;

fn main() {
    std::env::set_var("RUST_LOG", "info");
    env_logger::init();

    let config = config::cfg();

    let mut client = Client::connect(config.postgres.url.as_str(), NoTls).unwrap();

    let mut repository = ReadOnlyPostRepository {
        client: client.borrow_mut(),
    };

    fs::create_dir_all("drafts").unwrap();
    fs::create_dir_all("posts").unwrap();
    fs::write("slugs.sad", "").unwrap();

    let mut slugs = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open("slugs.sad")
        .unwrap();
    for post in repository.all() {
        match post {
            Post::NonExisting { .. } => {}
            Post::Draft {
                post_id,
                title,
                markdown_content,
                language,
                ..
            } => {
                let mut file = fs::OpenOptions::new()
                    .write(true)
                    .append(true)
                    .create_new(true)
                    .open(format!("drafts/{}.sad", post_id.to_str()))
                    .unwrap();
                let header = format!(
                    "title = \"{}\"\nlanguage = \"{}\"\n",
                    title,
                    language.to_string()
                );
                let separator = "---- sadraskol ----\n";
                let content = markdown_content.to_edit();
                write!(file, "{}", header).unwrap();
                write!(file, "{}", separator).unwrap();
                write!(file, "{}", content).unwrap();
            }
            Post::Post {
                title,
                markdown_content,
                language,
                publication_date,
                current_slug,
                previous_slugs,
                ..
            } => {
                let mut file = fs::OpenOptions::new()
                    .write(true)
                    .append(true)
                    .create_new(true)
                    .open(format!("posts/{}.sad", current_slug.as_str()))
                    .unwrap();
                let header = format!(
                    "title = \"{}\"\nlanguage = \"{}\"\npublication_date = \"{}\"\n",
                    title,
                    language.to_string(),
                    publication_date.to_rfc3339()
                );
                let separator = "---- sadraskol ----\n";
                let content = markdown_content.to_edit();
                write!(file, "{}", header).unwrap();
                write!(file, "{}", separator).unwrap();
                write!(file, "{}", content).unwrap();

                for previous_slug in previous_slugs {
                    slugs
                        .write_all(
                            format!(
                                "rewrite /posts/{} /posts/{} permanent;\n",
                                previous_slug,
                                current_slug.as_str()
                            )
                            .as_bytes(),
                        )
                        .unwrap();
                }
            }
        }
    }
}

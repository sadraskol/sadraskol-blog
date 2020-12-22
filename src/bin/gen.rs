extern crate askama;
extern crate sadraskol;

use std::fs;
use std::io::Write;

use askama::Template;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

use sadraskol::domain::slugify::slugify;
use sadraskol::domain::types::Markdown;
use sadraskol::web::BaseTemplate;

pub struct PostSummaryView {
    title: String,
    publication_date: String,
    language: String,
    view_link: String,
}

#[derive(Template)]
#[template(path = "index.html")]
struct IndexTemplate<'a> {
    _parent: BaseTemplate<'a>,
    posts: Vec<PostSummaryView>,
}

fn gen_home(posts: &Vec<SadPost>) {
    let v: Vec<_> = posts.iter()
        .map(|p| {
            PostSummaryView {
                title: p.title.clone(),
                language: p.language.to_string(),
                publication_date: p.publication_date.format("%d %B %Y").to_string(),
                view_link: format!("/posts/{}", slugify(p.title.clone())),
            }
        })
        .collect();

    let html = IndexTemplate {
        _parent: BaseTemplate::default(),
        posts: v,
    }.render().unwrap();

    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .create_new(true)
        .open("dist/index.html")
        .unwrap();

    write!(file, "{}", html).unwrap();
}


#[derive(Template)]
#[template(path = "feed.xml")]
struct FeedTemplate {
    posts: Vec<PostSummaryView>,
}

fn gen_feed(posts: &Vec<SadPost>) {
    let v: Vec<_> = posts.iter()
        .map(|p| {
            PostSummaryView {
                title: p.title.clone(),
                language: p.language.to_string(),
                publication_date: p.publication_date.to_rfc3339(),
                view_link: format!("/posts/{}", slugify(p.title.clone())),
            }
        })
        .collect();

    let html = FeedTemplate {
        posts: v,
    }.render().unwrap();

    fs::create_dir_all("dist/feed").unwrap();

    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .create_new(true)
        .open("dist/feed/index.xml")
        .unwrap();

    write!(file, "{}", html).unwrap();
}

#[derive(Template)]
#[template(path = "post.html")]
pub struct PostTemplate<'a> {
    pub _parent: BaseTemplate<'a>,
    pub title: String,
    pub publication_date: String,
    pub back_link: String,
    pub raw_content: String,
}

fn gen_post(post: &SadPost) {
    let page = PostTemplate {
        _parent: BaseTemplate::default(),
        title: post.title.clone(),
        publication_date: post.publication_date.format("%d %B %Y").to_string(),
        back_link: "/".to_string(),
        raw_content: post.saddown_content.format(),
    };

    let html = page.render().unwrap();

    fs::create_dir_all(format!("dist/posts/{}", slugify(post.title.clone()))).unwrap();

    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .create_new(true)
        .open(format!("dist/posts/{}/index.html", slugify(post.title.clone())))
        .unwrap();
    write!(file, "{}", html).unwrap();
}

fn gen_posts(posts: &Vec<SadPost>) {
    for x in posts {
        gen_post(x);
    }
}

fn gen_redirects() {
    fs::copy("slugs.sad", "dist/redirects").unwrap();
}


#[derive(Clone, Serialize, Deserialize)]
struct SadHeader {
    title: String,
    language: String,
    publication_date: String,
}

struct SadPost {
    title: String,
    language: String,
    publication_date: DateTime<Utc>,
    saddown_content: Markdown,
}

fn main() {
    let posts_files = fs::read_dir("posts").unwrap();
    let posts: Vec<SadPost> = posts_files
        .flat_map(|post| { post.map(|p| p.path()) })
        .map(|path| {
            let s = fs::read_to_string(path).unwrap();
            let v: Vec<_> = s.split("---- sadraskol ----").collect();
            let header: SadHeader = toml::from_str(v[0]).unwrap();
            let content = v[1];

            let date_time = DateTime::parse_from_rfc3339(header.publication_date.as_str())
                .ok()
                .map(|d| d.with_timezone(&Utc))
                .unwrap();

            SadPost {
                title: header.title,
                language: header.language,
                publication_date: date_time,
                saddown_content: Markdown::new(content),
            }
        })
        .collect();

    fs::create_dir_all("dist/posts").unwrap();

    gen_home(&posts);
    gen_feed(&posts);
    gen_posts(&posts);

    gen_redirects();
}
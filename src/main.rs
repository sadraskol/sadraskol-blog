extern crate askama;

use std::io::Write;
use std::path::PathBuf;

use askama::Template;

use crate::domain::slugify::slugify;
use crate::domain::types::SadPost;
use crate::fs::{read_post, FileDiff};
use crate::template::{FeedTemplate, IndexTemplate, PostSummaryView, PostTemplate};
use chrono::Utc;

mod custom_markdown;
mod domain;
mod fs;
mod highlight;
mod template;

fn gen_home(posts: &[SadPost]) {
    let v: Vec<_> = posts
        .iter()
        .map(|p| PostSummaryView::for_human(p))
        .collect();

    let html: String = IndexTemplate::new(v).render().unwrap();

    let mut file = FileDiff::new("dist/index.html");
    file.write_diff(html);
}

fn gen_feed(posts: &[SadPost]) {
    let v: Vec<_> = posts
        .iter()
        .map(|p| PostSummaryView::for_robot(p))
        .collect();

    let xml = FeedTemplate { posts: v }.render().unwrap();

    let mut file = FileDiff::new("dist/feed");
    file.write_diff(xml);
}

fn gen_post(post: &SadPost) {
    let page = PostTemplate {
        has_image: post.image.is_some(),
        image: &post.image.as_deref().unwrap_or(""),
        title: &post.title.clone(),
        publication_date: &post.publication_date.format("%d %B %Y").to_string(),
        back_link: "/",
        raw_content: &post.saddown_content.format(),
    };

    let html = page.render().unwrap();

    let mut file = FileDiff::new(format!("dist/posts/{}", slugify(post.title.clone())));
    file.write_diff(html);
}

fn gen_posts(posts: &[SadPost]) {
    std::fs::create_dir_all("dist/posts").unwrap();
    for x in posts {
        gen_post(x);
    }
}

fn gen_redirects() {
    std::fs::copy("slugs.sad", "dist/redirects").unwrap();
}

fn gen_assets() {
    std::fs::create_dir_all("dist/img").unwrap();
    for file in std::fs::read_dir("img").unwrap() {
        let origin_file = file.unwrap();
        let origin = origin_file.path();
        std::fs::copy(
            origin.as_path(),
            PathBuf::from("dist/img").join(origin_file.file_name()),
        )
        .unwrap();
    }
}

fn gen() {
    let now = Utc::now();
    let posts_files = std::fs::read_dir("posts").unwrap();
    let mut posts: Vec<SadPost> = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .map(|path| read_post(path.as_path()))
        .filter(|p| p.publication_date.date() <= now.date())
        .collect();
    posts.sort_by(|l, r| l.publication_date.cmp(&r.publication_date).reverse());

    gen_home(&posts);
    gen_feed(&posts);
    gen_posts(&posts);

    gen_redirects();
    gen_assets();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "gen" {
        gen();
    } else if args.len() > 1 && args[1] == "new" {
        if args.len() < 3 {
            eprintln!("missing [title] argument to new command");
            return;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(format!("posts/{}.sad", slugify(args[2].clone())))
            .unwrap();

        writeln!(f, "title=\"{}\"", args[2]).unwrap();
        writeln!(
            f,
            "publication_date=\"{}\"",
            chrono::Utc::now().to_rfc3339()
        )
        .unwrap();
        writeln!(f, "language=\"en\"").unwrap();
        writeln!(f, "---- sadraskol ----").unwrap();
    } else if args.len() > 1 && args[1] == "mv" {
        if args.len() < 3 {
            eprintln!("missing [from] argument to mv command");
            return;
        }
        if args.len() < 4 {
            eprintln!("missing [dest] argument to mv command");
            return;
        }
        let mut dest = std::fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(format!("posts/{}.sad", slugify(args[3].clone())))
            .unwrap();
        let from_file = format!("posts/{}.sad", args[2].clone());

        writeln!(dest, "title=\"{}\"", args[3]).unwrap();
        let str = std::fs::read_to_string(&from_file).unwrap();
        for line in str.lines().skip(1) {
            writeln!(dest, "{}", line).unwrap();
        }

        let mut redirects = std::fs::OpenOptions::new()
            .append(true)
            .write(true)
            .create(false)
            .create_new(false)
            .open("slugs.sad")
            .unwrap();

        writeln!(
            redirects,
            "rewrite /posts/{} /posts/{} permanent;",
            slugify(args[2].clone()),
            slugify(args[3].clone())
        )
        .unwrap();
        std::fs::remove_file(&from_file).unwrap();
    } else {
        println!("Help sadraskol blog cli");
        println!("\thelp - print this help");
        println!("\tgen - generate static site in dist/");
        println!("\tnew [title] - new article with title [title]");
        println!("\tmv [from] [dest] - move [from](slug) article to [dest] title, with correct redirects");
    }
}

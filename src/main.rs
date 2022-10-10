#[macro_use]
extern crate rocket;
extern crate askama;

use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::str::FromStr;

use askama::Template;

use crate::domain::date::Date;
use crate::domain::slugify::slugify;
use crate::domain::types::SadPost;
use crate::fs::{read_post, FileDiff};
use crate::template::{FeedTemplate, IndexTemplate, PostSummaryView, PostTemplate};

mod custom_markdown;
mod domain;
mod fs;
mod highlight;
mod preview;
mod template;

fn gen_home(posts: &[SadPost]) {
    let v: Vec<_> = posts.iter().map(PostSummaryView::for_human).collect();

    let html: String = IndexTemplate::new(v).render().unwrap();

    let mut file = FileDiff::new("dist/index.html");
    file.write_diff(html);
}

fn gen_feed(posts: &[SadPost]) {
    let v: Vec<_> = posts.iter().map(PostSummaryView::for_robot).collect();

    let xml = FeedTemplate { posts: v }.render().unwrap();

    std::fs::create_dir_all("dist/feed").unwrap();
    let mut file = FileDiff::new("dist/feed/index.xml");
    file.write_diff(xml);
}

fn gen_post(post: &SadPost) {
    let page = PostTemplate {
        title: &post.title.clone(),
        publication_date: &post.publication_date.human_format(&post.language),
        back_link: "/",
        raw_content: &post.saddown_content.format(),
    };

    let html = page.render().unwrap();

    std::fs::create_dir_all(format!("dist/posts/{}", slugify(&post.title))).unwrap();
    let mut file = FileDiff::new(format!("dist/posts/{}/index.html", slugify(&post.title)));
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

    std::fs::copy("favicon.ico", "dist/favicon.ico").unwrap();
}

fn gen_slides() {
    std::fs::create_dir_all("dist/slides").unwrap();

    fn visit_dirs<P: AsRef<std::path::Path>>(
        dir: P,
        cb: &dyn Fn(&std::fs::DirEntry),
    ) -> std::io::Result<()> {
        let dir = dir.as_ref();
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    visit_dirs(&path, cb)?;
                } else {
                    cb(&entry);
                }
            }
        }
        Ok(())
    }
    fn copy_file(f: &std::fs::DirEntry) {
        let buf = f.path();
        let relative_path = buf.strip_prefix("slides").unwrap();
        std::fs::create_dir_all(PathBuf::from("dist/slides").join(relative_path.parent().unwrap()))
            .unwrap();
        std::fs::copy(f.path(), PathBuf::from("dist/slides").join(relative_path)).unwrap();
    }
    visit_dirs("slides", &copy_file).unwrap();
}

fn gen() {
    let now = Date::now();
    let posts_files = std::fs::read_dir("posts").unwrap();
    let mut posts: Vec<SadPost> = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .map(|path| read_post(path.as_path()))
        .filter(|p| p.publication_date <= now)
        .collect();
    posts.sort_by_key(|p| p.publication_date.clone());
    posts.reverse();

    gen_home(&posts);
    gen_feed(&posts);
    gen_posts(&posts);

    gen_redirects();
    gen_assets();
    gen_slides();
}

#[rocket::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "preview" {
        preview::server().await;
    } else if args[1] == "publish" {
        let now = Date::now();
        let posts_files = std::fs::read_dir("posts").unwrap();
        let drafts: Vec<_> = posts_files
            .flat_map(|post| post.map(|p| p.path()))
            .map(|p| read_post(p.as_path()))
            .filter(|p| p.publication_date > now)
            .collect();
        if drafts.is_empty() {
            println!("no draft to publish");
        } else {
            println!("Choose the draft to publish:");
            for (i, draft) in drafts.iter().enumerate() {
                println!("\t{}: {}", i, draft.title);
            }
            let stdin = std::io::stdin();
            let mut buf = String::new();
            stdin.lock().read_line(&mut buf).unwrap();
            let i = usize::from_str(buf.to_string().trim()).unwrap();
            let mut draft: SadPost = drafts[i].clone();
            draft.publication_date = now;

            let mut f = std::fs::OpenOptions::new()
                .create(true)
                .write(true)
                .open(format!("posts/{}.sad", slugify(&draft.title)))
                .unwrap();

            writeln!(f, "title=\"{}\"", draft.title).unwrap();
            writeln!(
                f,
                "publication_date=\"{}\"",
                draft.publication_date.to_rfc3339()
            )
            .unwrap();
            writeln!(f, "language=\"{}\"", draft.language).unwrap();
            writeln!(f, "---- sadraskol ----").unwrap();
            writeln!(f, "{}", draft.saddown_content.raw()).unwrap();
        }
    } else if args.len() > 1 && args[1] == "drafts" {
        let now = Date::now();
        let posts_files = std::fs::read_dir("posts").unwrap();
        let drafts: Vec<_> = posts_files
            .flat_map(|post| post.map(|p| p.path()))
            .filter(|path| {
                let p = read_post(path.as_path());
                p.publication_date > now
            })
            .collect();
        for draft in drafts {
            println!("{}", draft.to_str().unwrap());
        }
    } else if args.len() > 1 && args[1] == "gen" {
        gen();
    } else if args.len() > 1 && args[1] == "new" {
        if args.len() < 3 {
            eprintln!("missing [title] argument to new command");
            return;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(format!("posts/{}.sad", slugify(&args[2])))
            .unwrap();

        writeln!(f, "title=\"{}\"", args[2]).unwrap();
        writeln!(
            f,
            "publication_date=\"{}\"",
            (chrono::Utc::now() + chrono::Duration::days(30)).to_rfc3339()
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
            .open(format!("posts/{}.sad", slugify(&args[3])))
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
            slugify(&args[2]),
            slugify(&args[3])
        )
        .unwrap();
        std::fs::remove_file(&from_file).unwrap();
    } else {
        println!("Help sadraskol blog cli");
        println!("\tdrafts - list posts not published yet");
        println!("\tgen - generate static site in dist/");
        println!("\thelp - print this help");
        println!("\tmv [from] [dest] - move [from](slug) article to [dest] title, with correct redirects");
        println!("\tnew [title] - new article with title [title]");
        println!("\tpreview - open firefox to display a live reloading preview of articles");
        println!("\tpublish - tool to include some draft in the next release");
    }
}

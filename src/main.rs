extern crate askama;

use std::fs;

use askama::Template;

use sadraskol::domain::slugify::slugify;
use sadraskol::domain::types::SadPost;
use sadraskol::fs::{read_post, FileDiff};
use sadraskol::template::{
    BaseTemplate, FeedTemplate, IndexTemplate, PostSummaryView, PostTemplate,
};

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
        _parent: BaseTemplate::default(),
        title: post.title.clone(),
        publication_date: post.publication_date.format("%d %B %Y").to_string(),
        back_link: "/".to_string(),
        raw_content: post.saddown_content.format(),
    };

    let html = page.render().unwrap();

    let mut file = FileDiff::new(format!("dist/posts/{}", slugify(post.title.clone())));
    file.write_diff(html);
}

fn gen_posts(posts: &[SadPost]) {
    fs::create_dir_all("dist/posts").unwrap();
    for x in posts {
        gen_post(x);
    }
}

fn gen_redirects() {
    fs::copy("slugs.sad", "dist/redirects").unwrap();
}

fn main() {
    let posts_files = fs::read_dir("posts").unwrap();
    let mut posts: Vec<SadPost> = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .map(|path| read_post(path.as_path()))
        .collect();
    posts.sort_by(|l, r| l.publication_date.cmp(&r.publication_date).reverse());

    gen_home(&posts);
    gen_feed(&posts);
    gen_posts(&posts);

    gen_redirects();
}

use std::process::Command;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::channel;
use std::time::Duration;
use notify::{DebouncedEvent, RecursiveMode, watcher, Watcher};
use rocket::http::{ContentType, Status};
use rocket::log::LogLevel;
use rocket::State;
use askama::Template;
use crate::{IndexTemplate, PostSummaryView, PostTemplate, read_post, SadPost, slugify};

#[get("/")]
fn home_page() -> (ContentType, String) {
    let posts_files = std::fs::read_dir("posts").unwrap();
    let mut posts: Vec<SadPost> = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .map(|path| read_post(path.as_path()))
        .collect();
    posts.sort_by_key(|p| p.publication_date.clone());
    posts.reverse();

    let v: Vec<_> = posts.iter().map(PostSummaryView::for_human).collect();

    let html: String = IndexTemplate::new(v).render().unwrap();

    (ContentType::HTML, introduce_script(html))
}

#[get("/posts/<slugs>")]
fn post_page(slugs: String) -> (ContentType, String) {
    let posts_files = std::fs::read_dir("posts").unwrap();
    let post = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .map(|path| read_post(path.as_path()))
        .find(|p| slugify(&p.title) == slugs)
        .expect("no post");
    let page = PostTemplate {
        has_image: post.image.is_some(),
        image: post.image.as_deref().unwrap_or(""),
        title: &post.title.clone(),
        publication_date: &post.publication_date.human_format(&post.language),
        back_link: "/",
        raw_content: &post.saddown_content.format(),
    };

    let html: String = page.render().unwrap();

    (ContentType::HTML, introduce_script(html))
}

fn introduce_script(original: String) -> String {
    let script = "<script>
        setInterval(() => {
            fetch('/__changes')
                .then(res => { if (res.status === 200) { location.reload(); } })
                .catch(e => {});
        }, 2000)</script></body>";
    original.replace("</body>", script)
}

#[get("/favicon.ico")]
fn favicon() -> (ContentType, Vec<u8>) {
    let content = std::fs::read("favicon.ico").unwrap();
    (ContentType::Icon, content)
}

#[get("/img/<img>")]
fn img(img: String) -> (ContentType, Vec<u8>) {
    let content = std::fs::read(format!("img/{}", img)).unwrap();
    (ContentType::JPEG, content)
}

#[get("/__changes")]
fn changes(reload: &State<Reload>) -> (Status, String) {
    let mut d = reload.0.lock().unwrap();
    if *d {
        *d = false;
        (Status::Ok, "reload".to_string())
    } else {
        (Status::NotModified, "".to_string())
    }
}

#[derive(Clone)]
struct Reload(Arc<Mutex<bool>>);

pub async fn server() {
    Command::new("firefox-esr")
        .args(["http://localhost:8000"])
        .spawn()
        .expect("could not open browser");

    let reload = Reload(Arc::new(Mutex::new(false)));
    let trigger = reload.clone();

    rocket::tokio::spawn(async move {
        let (sender, receiver) = channel();
        let mut watcher = watcher(sender, Duration::from_secs(10)).unwrap();
        watcher.watch("posts", RecursiveMode::Recursive).unwrap();
        loop {
            match receiver.recv() {
                Ok(event) => {
                    match event {
                        DebouncedEvent::Write(_) => {}
                        _ => {
                            let mut d = trigger.0.lock().unwrap();
                            *d = true;
                        }
                    }
                },
                Err(_e) => {},
            }
        }
    });

    let mut r = rocket::Config::default();
    r.log_level = LogLevel::Critical;

    rocket::build()
        .mount("/", routes![home_page, post_page, img, favicon, changes])
        .manage(reload)
        .configure(r)
        .launch()
        .await
        .unwrap();
}
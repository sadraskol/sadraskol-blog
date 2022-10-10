use crate::{read_post, slugify, IndexTemplate, PostSummaryView, PostTemplate, SadPost};
use askama::Template;
use notify::{watcher, DebouncedEvent, RecursiveMode, Watcher};
use rocket::fairing::AdHoc;
use rocket::http::{ContentType, Status};
use rocket::log::LogLevel;
use rocket::State;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::time::Duration;

#[get("/")]
fn home_page() -> (ContentType, String) {
    let posts_files = std::fs::read_dir("posts").unwrap();
    let mut posts: Vec<SadPost> = posts_files
        .flat_map(|post| post.map(|p| p.path()))
        .filter(|p| p.extension().map(|p| p == "sad").unwrap_or(false))
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
        .filter(|p| p.extension().map(|p| p == "sad").unwrap_or(false))
        .map(|path| read_post(path.as_path()))
        .find(|p| slugify(&p.title) == slugs)
        .expect("no post");
    let page = PostTemplate {
        title: &post.title,
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
    let d = reload.0.load(Ordering::Acquire);
    if d {
        reload.0.store(false, Ordering::Release);
        (Status::Ok, "reload".to_string())
    } else {
        (Status::NotModified, "".to_string())
    }
}

#[derive(Clone)]
struct Reload(Arc<AtomicBool>);

#[allow(unused_must_use)]
pub async fn server() {
    use std::net::TcpListener;
    let mut candidate = 3000;
    let port = loop {
        if TcpListener::bind(("127.0.0.1", candidate)).is_ok() {
            break candidate;
        }
        candidate += 1;
    };

    Command::new("firefox-esr")
        .args([format!("http://localhost:{port}")])
        .spawn()
        .expect("could not open browser");

    let reload = Reload(Arc::new(AtomicBool::new(false)));
    let trigger = reload.clone();

    let r = rocket::Config {
        log_level: LogLevel::Critical,
        port,
        ..rocket::Config::default()
    };

    rocket::build()
        .mount("/", routes![home_page, post_page, img, favicon, changes])
        .manage(reload)
        .configure(r)
        .attach(AdHoc::on_liftoff("reload_fairing", |r| {
            Box::pin(async move {
                let shutdown = r.shutdown();
                rocket::tokio::spawn(async move {
                    let abort = Arc::new(AtomicBool::new(false));
                    let t_abort = abort.clone();
                    rocket::tokio::spawn(async move {
                        let (sender, receiver) = channel();
                        let mut watcher = watcher(sender, Duration::from_secs(2)).unwrap();
                        watcher.watch("posts", RecursiveMode::Recursive).unwrap();
                        loop {
                            match receiver.recv_timeout(Duration::from_millis(100)) {
                                Ok(event) => match event {
                                    DebouncedEvent::Write(_) => {}
                                    _ => {
                                        trigger.0.store(true, Ordering::Release);
                                    }
                                },
                                Err(_e) => {
                                    if t_abort.load(Ordering::Acquire) {
                                        break;
                                    }
                                }
                            }
                        }
                    });
                    shutdown.await;
                    abort.store(true, Ordering::Release);
                });
            })
        }))
        .launch()
        .await
        .unwrap();
}

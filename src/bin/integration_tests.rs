extern crate sadraskol;

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use chrono::Timelike;
use postgres::{Client, NoTls};
use rand::Rng;

use sadraskol::domain::post::{InnerDraftDeleted, InnerDraftMadePublic, InnerDraftSubmitted, InnerPostEdited, InnerPostPublished, Post};
use sadraskol::domain::post::PostEvent::{DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostPublished};
use sadraskol::domain::repository::PostRepository;
use sadraskol::domain::types::{Language, Markdown, PostId};
use sadraskol::infra::post_repository::TransactionalPostRepository;

pub struct RepositoryTestContainer<'a> {
    pub name: &'a str,
    pub f: Box<dyn FnOnce(&mut TransactionalPostRepository) -> ()>,
}

fn test_publish_draft(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    let date = chrono::Utc::now()
        .with_nanosecond(0).unwrap();
    repo.save(PostPublished(InnerPostPublished {
        post_id,
        version: 1,
        slug: "post-slug".to_string(),
        publication_date: date,
    }));
    let expected_post = Post::Post {
        post_id,
        version: 2,
        title: "some title".to_string(),
        markdown_content: Markdown::new("some content"),
        language: Language::Fr,
        publication_date: date,
        current_slug: "post-slug".to_string(),
        previous_slugs: vec![],
    };
    assert_eq!(repo.all_posts(), vec![expected_post.clone()]);
    assert_eq!(repo.all_drafts(), vec![]);
    assert_eq!(repo.read(post_id), Some(expected_post.clone()));
}

fn test_finding_post_by_slug(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    assert_eq!(repo.find_by_slug(post_id.to_str()).is_some(), false);
    assert_eq!(repo.find_by_slug("some-title".to_string()).is_some(), false);
    assert_eq!(repo.find_by_slug("yet-another-title".to_string()).is_some(), false);
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    repo.save(DraftMadePublic(InnerDraftMadePublic { post_id, version: 0 }));
    assert_eq!(repo.find_by_slug(post_id.to_str()).is_some(), true);
    assert_eq!(repo.find_by_slug("some-title".to_string()).is_some(), false);
    assert_eq!(repo.find_by_slug("yet-another-title".to_string()).is_some(), false);
    let date = chrono::Utc::now()
        .with_nanosecond(0).unwrap();
    repo.save(PostPublished(InnerPostPublished {
        post_id,
        version: 1,
        slug: "some-title".to_string(),
        publication_date: date,
    }));
    assert_eq!(repo.find_by_slug(post_id.to_str()).is_some(), true);
    assert_eq!(repo.find_by_slug("some-title".to_string()).is_some(), true);
    assert_eq!(repo.find_by_slug("yet-another-title".to_string()).is_some(), false);
    repo.save(PostEdited(InnerPostEdited {
        post_id,
        version: 2,
        title: Some("yet another title".to_string()),
        slug: Some("yet-another-title".to_string()),
        markdown_content: "markdown again".to_string(),
        language: Language::En,
    }));
    assert_eq!(repo.find_by_slug(post_id.to_str()).is_some(), true);
    assert_eq!(repo.find_by_slug("some-title".to_string()).is_some(), true);
    assert_eq!(repo.find_by_slug("yet-another-title".to_string()).is_some(), true);
}

fn test_edit_post(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    let date = chrono::Utc::now()
        .with_nanosecond(0).unwrap();
    repo.save(PostPublished(InnerPostPublished {
        post_id,
        version: 1,
        slug: "post-slug".to_string(),
        publication_date: date,
    }));
    repo.save(PostEdited(InnerPostEdited {
        post_id,
        version: 2,
        title: Some("very other title".to_string()),
        slug: Some("very-old-slug".to_string()),
        markdown_content: "very other content".to_string(),
        language: Language::En,
    }));
    repo.save(PostEdited(InnerPostEdited {
        post_id,
        version: 3,
        title: Some("other title".to_string()),
        slug: Some("other-title".to_string()),
        markdown_content: "other content".to_string(),
        language: Language::En,
    }));
    let expected_post = Post::Post {
        post_id,
        version: 4,
        title: "other title".to_string(),
        markdown_content: Markdown::new("other content"),
        language: Language::En,
        publication_date: date,
        current_slug: "other-title".to_string(),
        previous_slugs: vec!["post-slug".to_string(), "very-old-slug".to_string()],
    };
    assert_eq!(repo.all_posts(), vec![expected_post.clone()]);
    assert_eq!(repo.all_drafts(), vec![]);
    assert_eq!(repo.read(post_id), Some(expected_post.clone()));
}

fn test_submit_non_existing_draft(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    let expected_draft = Post::Draft {
        post_id,
        version: 1,
        title: "some title".to_string(),
        markdown_content: Markdown::new("some content"),
        language: Language::Fr,
        shareable: false,
    };
    assert_eq!(repo.all_posts(), vec![]);
    assert_eq!(repo.all_drafts(), vec![expected_draft.clone()]);
    assert_eq!(repo.read(post_id), Some(expected_draft.clone()));
}

fn test_edit_draft(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 1,
        title: "other title".to_string(),
        markdown_content: "other content".to_string(),
        language: Language::En,
    }));
    let expected_draft = Post::Draft {
        post_id,
        version: 2,
        title: "other title".to_string(),
        markdown_content: Markdown::new("other content"),
        language: Language::En,
        shareable: false,
    };
    assert_eq!(repo.all_posts(), vec![]);
    assert_eq!(repo.all_drafts(), vec![expected_draft.clone()]);
    assert_eq!(repo.read(post_id), Some(expected_draft.clone()));
}

fn test_make_draft_public(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    repo.save(DraftMadePublic(InnerDraftMadePublic { post_id, version: 0 }));
    let expected_draft = Post::Draft {
        post_id,
        version: 1,
        title: "some title".to_string(),
        markdown_content: Markdown::new("some content"),
        language: Language::Fr,
        shareable: true,
    };
    assert_eq!(repo.all_posts(), vec![]);
    assert_eq!(repo.all_drafts(), vec![expected_draft.clone()]);
    assert_eq!(repo.read(post_id), Some(expected_draft.clone()));
}

fn test_delete_draft(repo: &mut TransactionalPostRepository) {
    let post_id = PostId::new(uuid::Uuid::new_v4());
    repo.save(DraftSubmitted(InnerDraftSubmitted {
        post_id,
        version: 0,
        title: "some title".to_string(),
        markdown_content: "some content".to_string(),
        language: Language::Fr,
    }));
    repo.save(DraftDeleted(InnerDraftDeleted { post_id, version: 1 }));
    assert_eq!(repo.all_posts(), vec![]);
    assert_eq!(repo.all_drafts(), vec![]);
    assert_eq!(repo.read(post_id), None);
}

fn main() {
    run_with_database(vec![
        RepositoryTestContainer { name: "submit_non_existing_draft", f: Box::new(test_submit_non_existing_draft) },
        RepositoryTestContainer { name: "edit_draft", f: Box::new(test_edit_draft) },
        RepositoryTestContainer { name: "make_draft_public", f: Box::new(test_make_draft_public) },
        RepositoryTestContainer { name: "delete_draft", f: Box::new(test_delete_draft) },
        RepositoryTestContainer { name: "publish_draft", f: Box::new(test_publish_draft) },
        RepositoryTestContainer { name: "edit_post", f: Box::new(test_edit_post) },
        RepositoryTestContainer { name: "find_post_or_draft_by_slug", f: Box::new(test_finding_post_by_slug) }
    ]);
}

fn run_with_database(containers: Vec<RepositoryTestContainer>) {
    let mut rng = rand::thread_rng();
    let port = rng.gen_range(30000, 50000);

    let output = Command::new("docker")
        .arg("run")
        .arg("-d")
        .arg("-p").arg(port.to_string() + ":5432")
        .arg("--tmpfs").arg("/var/lib/postgresql/data:rw")
        .arg("postgres:10.4").arg("-c").arg("fsync=off")
        .output()
        .expect("process failed to execute");
    while Client::connect(format!("postgres://postgres@localhost:{}", port).as_str(), NoTls).is_err() {
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("sadraskol.sql");
    let mut connection = Client::connect(format!("postgres://postgres@localhost:{}", port).as_str(), NoTls).unwrap();
    let contents = fs::read_to_string(d).unwrap();
    for container in containers {
        let mut transaction = connection.transaction().unwrap();
        transaction.batch_execute(contents.as_str()).unwrap();
        println!("{}", container.name);
        (container.f)(&mut TransactionalPostRepository { transaction });
    }

    let process_to_kill = std::str::from_utf8(output.stdout.as_slice())
        .unwrap()
        .trim();

    Command::new("docker")
        .arg("kill")
        .arg(process_to_kill)
        .status()
        .unwrap()
        .code();
}
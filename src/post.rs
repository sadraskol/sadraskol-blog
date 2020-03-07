use std::str::FromStr;

use chrono::{DateTime, Utc};
use pulldown_cmark::{Options, Parser};

use crate::custom_markdown::sad_push_html;
use crate::post::PostEvent::{DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostError, PostPublished};
use crate::slugify::slugify;

pub type AggregateId = uuid::Uuid;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Language { Fr, En }

impl FromStr for Language {
    type Err = ();

    fn from_str(s: &str) -> Result<Language, ()> {
        match s {
            "fr" => Ok(Language::Fr),
            "en" => Ok(Language::En),
            _ => Err(()),
        }
    }
}

impl ToString for Language {
    fn to_string(&self) -> String {
        return match self {
            Language::Fr => "fr".to_string(),
            Language::En => "en".to_string(),
        };
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Markdown {
    raw: String
}

impl Markdown {
    pub fn new<T: ToString>(value: T) -> Markdown {
        Markdown { raw: value.to_string() }
    }

    pub fn format(&self) -> String {
        let mut options = Options::empty();
        options.insert(Options::ENABLE_STRIKETHROUGH);
        options.insert(Options::ENABLE_TABLES);
        let mut parser = Parser::new_ext(self.raw.as_str(), options);

        let mut html_output: String = String::with_capacity(self.raw.len() * 2);
        sad_push_html(&mut html_output, &mut parser);
        html_output.clone()
    }

    pub fn to_edit(&self) -> String {
        self.raw.clone()
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Post {
    NonExisting {
        aggregate_id: AggregateId,
    },
    Draft {
        aggregate_id: AggregateId,
        version: u32,
        title: String,
        markdown_content: Markdown,
        language: Language,
        shareable: bool,
    },
    Post {
        aggregate_id: AggregateId,
        version: u32,
        title: String,
        markdown_content: Markdown,
        language: Language,
        publication_date: DateTime<Utc>,
        current_slug: String,
        previous_slugs: Vec<String>,
    },
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum PostEvent {
    DraftDeleted(InnerDraftDeleted),
    PostPublished(InnerPostPublished),
    DraftSubmitted(InnerDraftSubmitted),
    PostEdited(InnerPostEdited),
    DraftMadePublic(InnerDraftMadePublic),
    PostError(PostErrors),
}

#[cfg(test)]
impl PostEvent {
    fn is_err(&self) -> bool {
        match self {
            PostError(_) => true,
            _ => false,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerDraftDeleted {
    pub aggregate_id: AggregateId,
    pub version: u32,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerPostPublished {
    pub aggregate_id: AggregateId,
    pub version: u32,
    pub slug: String,
    pub publication_date: DateTime<Utc>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerDraftSubmitted {
    pub aggregate_id: AggregateId,
    pub version: u32,
    pub title: String,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerPostEdited {
    pub aggregate_id: AggregateId,
    pub version: u32,
    pub title: Option<String>,
    pub slug: Option<String>,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerDraftMadePublic {
    pub aggregate_id: AggregateId,
    pub version: u32,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum PostErrors {
    CannotDelete,
    CannotPublish,
    CannotEditPost,
    CannotMakePublic,
    AlreadyPublic,
    CannotEditDraftAsPost,
    UnknownSlug,
    CurrentSlugIsNow(String),
}

impl std::string::ToString for PostErrors {
    fn to_string(&self) -> String {
        return match self {
            PostErrors::CannotDelete => "CannotDelete".to_string(),
            PostErrors::CannotPublish => "CannotPublish".to_string(),
            PostErrors::CannotEditPost => "CannotEditPost".to_string(),
            PostErrors::CannotMakePublic => "CannotMakePublic".to_string(),
            PostErrors::AlreadyPublic => "AlreadyPublic".to_string(),
            PostErrors::CannotEditDraftAsPost => "CannotEditDraftAsPost".to_string(),
            PostErrors::UnknownSlug => "UnknownSlug".to_string(),
            PostErrors::CurrentSlugIsNow(current) => format!("CurrentSlugIsNow({})", current),
        };
    }
}

impl Post {
    pub fn aggregate_id(&self) -> AggregateId {
        return match self {
            Post::NonExisting { aggregate_id } => aggregate_id.clone(),
            Post::Draft { aggregate_id, .. } => aggregate_id.clone(),
            Post::Post { aggregate_id, .. } => aggregate_id.clone(),
        };
    }

    pub fn version(&self) -> u32 {
        return match self {
            Post::NonExisting { .. } => 0,
            Post::Draft { version, .. } => version.clone(),
            Post::Post { version, .. } => version.clone(),
        };
    }

    pub fn title(&self) -> Option<String> {
        return match self {
            Post::NonExisting { .. } => None,
            Post::Draft { title, .. } => Some(title.clone()),
            Post::Post { title, .. } => Some(title.clone()),
        };
    }

    pub fn check_current_slug(&self, slug: String) -> Result<Self, PostErrors> {
        return match self {
            Post::NonExisting { .. } => Ok(self.clone()),
            Post::Draft { aggregate_id, shareable, .. } => {
                if *shareable && aggregate_id.to_hyphenated().to_string() == slug.clone() {
                    Ok(self.clone())
                } else {
                    Err(PostErrors::UnknownSlug)
                }
            }
            Post::Post { current_slug, previous_slugs, .. } => {
                if *current_slug == slug {
                    Ok(self.clone())
                } else if previous_slugs.contains(&slug) {
                    Err(PostErrors::CurrentSlugIsNow(current_slug.clone()))
                } else {
                    Err(PostErrors::UnknownSlug)
                }
            }
        };
    }

    pub fn submit_draft<S: Into<String>, V: Into<String>>(
        &self,
        language: Language,
        title: S,
        markdown_content: V,
    ) -> PostEvent {
        return match self {
            Post::Post { .. } => PostError(PostErrors::CannotEditPost),
            _ => DraftSubmitted(InnerDraftSubmitted {
                aggregate_id: self.aggregate_id(),
                version: self.version(),
                title: title.into(),
                markdown_content: markdown_content.into(),
                language,
            }),
        };
    }

    pub fn make_public(&self) -> PostEvent {
        return match self {
            Post::Draft { shareable: false, .. } => DraftMadePublic(InnerDraftMadePublic { aggregate_id: self.aggregate_id(), version: self.version() }),
            Post::Draft { shareable: true, .. } => PostError(PostErrors::AlreadyPublic),
            Post::Post { .. } => PostError(PostErrors::CannotMakePublic),
            Post::NonExisting { .. } => PostError(PostErrors::CannotMakePublic),
        };
    }

    pub fn delete_draft(&self) -> PostEvent {
        return match self {
            Post::Draft { .. } => DraftDeleted(InnerDraftDeleted { aggregate_id: self.aggregate_id(), version: self.version() }),
            Post::Post { .. } => PostError(PostErrors::CannotDelete),
            Post::NonExisting { .. } => PostError(PostErrors::CannotDelete),
        };
    }

    pub fn publish_draft(&self, publication_date: DateTime<Utc>) -> PostEvent {
        return match self {
            Post::Draft { title, .. } =>
                PostPublished(InnerPostPublished {
                    aggregate_id: self.aggregate_id(),
                    version: self.version(),
                    slug: slugify(title.clone()),
                    publication_date,
                }),
            Post::Post { .. } => PostError(PostErrors::CannotPublish),
            Post::NonExisting { .. } => PostError(PostErrors::CannotPublish),
        };
    }

    pub fn edit_post<Title: Into<String>, Content: Into<String>>(
        &self,
        language: Language,
        new_title: Title,
        markdown_content: Content,
    ) -> PostEvent {
        return match self {
            Post::Draft { .. } => PostError(PostErrors::CannotEditDraftAsPost),
            Post::Post { title, current_slug, .. } => {
                let new_title_as_string = new_title.into();
                let maybe_title_changed = if title.clone() == new_title_as_string {
                    None
                } else {
                    Some(new_title_as_string.clone())
                };
                let maybe_slug_changed = if slugify(new_title_as_string.clone()) == *current_slug {
                    None
                } else {
                    Some(slugify(new_title_as_string.clone()))
                };
                return PostEdited(InnerPostEdited {
                    aggregate_id: self.aggregate_id(),
                    version: self.version(),
                    language,
                    title: maybe_title_changed,
                    slug: maybe_slug_changed,
                    markdown_content: markdown_content.into(),
                });
            }
            Post::NonExisting { .. } => PostError(PostErrors::CannotEditDraftAsPost),
        };
    }
}

#[cfg(test)]
mod test {
    use rand::{Rng, thread_rng};
    use rand::distributions::Alphanumeric;
    use rand::distributions::Distribution;
    use rand::distributions::Uniform;

    use crate::post::{InnerDraftDeleted, InnerDraftMadePublic, InnerDraftSubmitted, InnerPostEdited, InnerPostPublished, Markdown};
    use crate::post::Language;
    use crate::post::Post;
    use crate::post::PostErrors;
    use crate::post::PostEvent::{DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostError, PostPublished};

    #[test]
    fn submit_draft_successfully() {
        let no_post = Post::NonExisting { aggregate_id: uuid::Uuid::new_v4() };
        assert_eq!(
            no_post.submit_draft(Language::Fr, "some title", "some content"),
            DraftSubmitted(InnerDraftSubmitted {
                aggregate_id: no_post.aggregate_id(),
                version: no_post.version(),
                title: "some title".to_string(),
                markdown_content: "some content".to_string(),
                language: Language::Fr,
            })
        );
    }

    #[test]
    fn edit_draft_keeps_public_status() {
        let draft = random_shareable_draft();
        assert_eq!(
            draft.submit_draft(Language::Fr, "some title", "some content"),
            DraftSubmitted(InnerDraftSubmitted {
                aggregate_id: draft.aggregate_id(),
                version: draft.version(),
                title: "some title".to_string(),
                markdown_content: "some content".to_string(),
                language: Language::Fr,
            })
        );
    }

    #[test]
    fn cannot_edit_post_with_draft() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.submit_draft(Language::Fr, "some title", "some content"),
            PostError(PostErrors::CannotEditPost)
        );
    }

    #[test]
    fn deleting_a_draft() {
        let draft = random_draft();
        assert_eq!(
            draft.delete_draft(),
            DraftDeleted(InnerDraftDeleted { aggregate_id: draft.aggregate_id(), version: draft.version() })
        );
    }

    #[test]
    fn cannot_delete_a_post() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.delete_draft(),
            PostError(PostErrors::CannotDelete)
        );
    }

    #[test]
    fn publish_a_draft() {
        let publication_date = chrono::Utc::now();
        let draft = random_draft();
        assert_eq!(
            draft.publish_draft(publication_date),
            PostPublished(InnerPostPublished {
                aggregate_id: draft.aggregate_id(),
                version: draft.version(),
                slug: crate::slugify::slugify(draft.title().unwrap()),
                publication_date,
            })
        );
    }

    #[test]
    fn cannot_publish_a_post() {
        let publication_date = chrono::Utc::now();
        let post = PostBuilder::new().build();
        assert_eq!(
            post.publish_draft(publication_date),
            PostError(PostErrors::CannotPublish)
        );
    }

    #[test]
    fn make_draft_public() {
        let draft = random_draft();
        assert_eq!(
            draft.make_public(),
            DraftMadePublic(InnerDraftMadePublic { aggregate_id: draft.aggregate_id(), version: draft.version() })
        );
    }

    #[test]
    fn cannot_make_public_twice() {
        let draft = random_shareable_draft();
        assert_eq!(
            draft.make_public(),
            PostError(PostErrors::AlreadyPublic)
        );
    }

    #[test]
    fn cannot_make_public_a_post() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.make_public(),
            PostError(PostErrors::CannotMakePublic)
        );
    }

    #[test]
    fn edit_a_post_will_not_change_title_if_not_necessary() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.edit_post(Language::En, post.title().unwrap(), "other content"),
            PostEdited(InnerPostEdited {
                aggregate_id: post.aggregate_id(),
                version: post.version(),
                title: None,
                slug: None,
                markdown_content: "other content".to_string(),
                language: Language::En,
            })
        );
    }

    #[test]
    fn edit_a_post_changes_the_title_if_necessary() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.edit_post(Language::En, "another title", "other content"),
            PostEdited(InnerPostEdited {
                aggregate_id: post.aggregate_id(),
                version: post.version(),
                title: Some("another title".to_string()),
                slug: Some("another-title".to_string()),
                markdown_content: "other content".to_string(),
                language: Language::En,
            })
        );
    }

    #[test]
    fn edit_a_post_changing_its_slug_but_not_the_title() {
        let post = PostBuilder::new()
            .title("What a title!")
            .build();
        assert_eq!(
            post.edit_post(Language::En, "What a title!", "other content"),
            PostEdited(InnerPostEdited {
                aggregate_id: post.aggregate_id(),
                version: post.version(),
                title: None,
                slug: Some("what-a-title".to_string()),
                markdown_content: "other content".to_string(),
                language: Language::En,
            })
        );
    }

    #[test]
    fn cannot_edit_draft_as_post() {
        let draft = random_draft();
        assert_eq!(
            draft.edit_post(Language::En, "another title", "other content"),
            PostError(PostErrors::CannotEditDraftAsPost)
        );
    }

    #[test]
    fn cannot_perform_any_operation_on_non_existing_expect_submitting_a_draft() {
        let no_post = Post::NonExisting { aggregate_id: uuid::Uuid::new_v4() };
        assert!(no_post.make_public().is_err());
        assert!(no_post.delete_draft().is_err());
        assert!(no_post.publish_draft(chrono::Utc::now()).is_err());
        assert!(no_post.edit_post(Language::En, rand_str(), rand_str()).is_err());
    }

    #[test]
    fn check_current_slug() {
        assert_eq!(random_draft().check_current_slug(rand_str()), Err(PostErrors::UnknownSlug));
        let draft = random_shareable_draft();
        assert_eq!(draft.clone().check_current_slug(rand_str()), Err(PostErrors::UnknownSlug));
        assert_eq!(
            draft.clone().check_current_slug(draft.aggregate_id().to_hyphenated().to_string()),
            Ok(draft.clone()));
        let post = PostBuilder::new()
            .with_slug("some-slug")
            .with_old_slugs(&["old-slug", "old-new-slug"])
            .build();
        assert_eq!(post.clone().check_current_slug(rand_str()), Err(PostErrors::UnknownSlug));
        assert_eq!(post.clone().check_current_slug("some-slug".to_string()), Ok(post.clone()));
        assert_eq!(
            post.clone().check_current_slug("old-slug".to_string()),
            Err(PostErrors::CurrentSlugIsNow("some-slug".to_string()))
        );
    }

    fn rand_str() -> String {
        let mut rng = rand::thread_rng();
        let length_gen = Uniform::from(1..100);
        return thread_rng()
            .sample_iter(&Alphanumeric)
            .take(length_gen.sample(&mut rng))
            .collect();
    }

    fn rand_version() -> u32 {
        let mut rng = rand::thread_rng();
        let die = Uniform::from(0..=100);
        return die.sample(&mut rng);
    }

    fn rand_lang() -> Language {
        let mut rng = rand::thread_rng();
        let die = Uniform::from(1..3);
        if die.sample(&mut rng) % 2 == 0 {
            return Language::Fr;
        } else {
            return Language::En;
        }
    }

    fn random_draft() -> Post {
        return Post::Draft {
            aggregate_id: uuid::Uuid::new_v4(),
            version: rand_version(),
            title: rand_str(),
            markdown_content: Markdown::new(rand_str()),
            language: rand_lang(),
            shareable: false,
        };
    }

    fn random_shareable_draft() -> Post {
        return Post::Draft {
            aggregate_id: uuid::Uuid::new_v4(),
            version: rand_version(),
            title: rand_str(),
            markdown_content: Markdown::new(rand_str()),
            language: rand_lang(),
            shareable: true,
        };
    }

    struct PostBuilder {
        aggregate_id: uuid::Uuid,
        version: u32,
        title: String,
        markdown_content: String,
        language: Language,
        publication_date: chrono::DateTime<chrono::Utc>,
        current_slug: String,
        previous_slugs: Vec<String>,
    }

    impl PostBuilder {
        fn new() -> PostBuilder {
            let title = rand_str();
            return PostBuilder {
                aggregate_id: uuid::Uuid::new_v4(),
                version: rand_version(),
                title: title.clone(),
                markdown_content: rand_str(),
                language: rand_lang(),
                publication_date: chrono::Utc::now(),
                current_slug: crate::slugify::slugify(title.clone()),
                previous_slugs: vec![],
            };
        }

        fn title(mut self, title: &str) -> Self {
            self.title = title.to_string();
            self
        }

        fn with_slug(mut self, slug: &str) -> Self {
            self.current_slug = slug.to_string();
            self
        }

        fn with_old_slugs(mut self, slugs: &[&str]) -> Self {
            self.previous_slugs = slugs.into_iter()
                .map(|s| s.to_string())
                .collect();
            self
        }

        fn build(&self) -> Post {
            return Post::Post {
                aggregate_id: self.aggregate_id.clone(),
                version: self.version.clone(),
                title: self.title.clone(),
                markdown_content: Markdown::new(self.markdown_content.clone()),
                language: self.language.clone(),
                publication_date: self.publication_date.clone(),
                current_slug: self.current_slug.clone(),
                previous_slugs: self.previous_slugs.clone(),
            };
        }
    }
}
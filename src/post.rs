extern crate either;

use std::str::FromStr;

use chrono::{DateTime, Utc};
use either::Either;

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
pub enum Post {
    NonExisting {
        aggregate_id: AggregateId,
    },
    Draft {
        aggregate_id: AggregateId,
        title: String,
        description: String,
        markdown_content: String,
        language: Language,
        shareable: bool,
    },
    Post {
        aggregate_id: AggregateId,
        title: String,
        description: String,
        markdown_content: String,
        language: Language,
        publication_date: DateTime<Utc>,
        current_slug: Slug,
        alternative_slugs: Vec<Slug>,
    },
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Slug { pub slug: String }

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct DraftDeleted {
    pub aggregate_id: AggregateId
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PostPublished {
    pub aggregate_id: AggregateId,
    pub slug: Slug,
    pub publication_date: DateTime<Utc>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct DraftSubmitted {
    pub aggregate_id: AggregateId,
    pub title: String,
    pub description: String,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PostEdited {
    pub aggregate_id: AggregateId,
    pub title: Option<String>,
    pub description: String,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct DraftMadePublic {
    pub aggregate_id: AggregateId
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum PostErrors {
    CannotDelete,
    CannotPublish,
    CannotEditPost,
    CannotMakePublic,
    AlreadyPublic,
    CannotEditDraftAsPost,
}

impl std::string::ToString for PostErrors {
    fn to_string(&self) -> String {
        return match self {
            PostErrors::CannotDelete => "CannotDelete".to_string(),
            PostErrors::CannotPublish => "CannotPublish".to_string(),
            PostErrors::CannotEditPost => "CannotEditPost".to_string(),
            PostErrors::CannotMakePublic => "CannotMakePublic".to_string(),
            PostErrors::AlreadyPublic => "AlreadyPublic".to_string(),
            PostErrors::CannotEditDraftAsPost => "CannotEditDraftAsPost".to_string()
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

    fn title(&self) -> Option<String> {
        return match self {
            Post::NonExisting { .. } => None,
            Post::Draft { title, .. } => Some(title.clone()),
            Post::Post { title, .. } => Some(title.clone()),
        };
    }

    pub fn submit_draft<S: Into<String>, T: Into<String>, V: Into<String>>(
        &self,
        language: Language,
        title: S,
        description: T,
        markdown_content: V,
    ) -> Result<DraftSubmitted, PostErrors> {
        return match self {
            Post::Post { .. } => Err(PostErrors::CannotEditPost),
            _ => Ok(DraftSubmitted {
                aggregate_id: self.aggregate_id(),
                title: title.into(),
                description: description.into(),
                markdown_content: markdown_content.into(),
                language,
            }),
        };
    }

    pub fn make_public(&self) -> Either<PostErrors, DraftMadePublic> {
        return match self {
            Post::Draft { shareable: false, .. } => either::Right(DraftMadePublic { aggregate_id: self.aggregate_id() }),
            Post::Draft { shareable: true, .. } => either::Left(PostErrors::AlreadyPublic),
            Post::Post { .. } => either::Left(PostErrors::CannotMakePublic),
            Post::NonExisting { .. } => either::Left(PostErrors::CannotMakePublic),
        };
    }

    pub fn delete_draft(&self) -> Either<PostErrors, DraftDeleted> {
        return match self {
            Post::Draft { .. } => either::Right(DraftDeleted { aggregate_id: self.aggregate_id() }),
            Post::Post { .. } => either::Left(PostErrors::CannotDelete),
            Post::NonExisting { .. } => either::Left(PostErrors::CannotDelete),
        };
    }

    pub fn publish_draft(&self, slug: Slug, publication_date: DateTime<Utc>) -> Either<PostErrors, PostPublished> {
        return match self {
            Post::Draft { .. } =>
                either::Right(PostPublished { aggregate_id: self.aggregate_id(), slug, publication_date }),
            Post::Post { .. } =>
                either::Left(PostErrors::CannotPublish),
            Post::NonExisting { .. } => either::Left(PostErrors::CannotPublish),
        };
    }

    pub fn edit_post<S: Into<String>, T: Into<String>, V: Into<String>>(
        &self,
        language: Language,
        new_title: S,
        description: T,
        markdown_content: V,
    ) -> Either<PostErrors, PostEdited> {
        return match self {
            Post::Draft { .. } => either::Left(PostErrors::CannotEditDraftAsPost),
            Post::Post { title, .. } => {
                let new_title_as_string = new_title.into();
                let maybe_title_changed = if title.clone() == new_title_as_string {
                    None
                } else {
                    Some(new_title_as_string.clone())
                };
                return either::Right(PostEdited {
                    aggregate_id: self.aggregate_id(),
                    language,
                    title: maybe_title_changed,
                    description: description.into(),
                    markdown_content: markdown_content.into(),
                });
            }
            Post::NonExisting { .. } => either::Left(PostErrors::CannotEditDraftAsPost),
        };
    }
}

#[cfg(test)]
mod test {
    use rand::{Rng, thread_rng};
    use rand::distributions::Alphanumeric;
    use rand::distributions::Distribution;
    use rand::distributions::Uniform;

    use crate::post::{DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostPublished, Slug};
    use crate::post::Language;
    use crate::post::Post;
    use crate::post::PostErrors;

    #[test]
    fn submit_draft_successfully() {
        let no_post = Post::NonExisting { aggregate_id: rand_str() };
        assert_eq!(
            no_post.submit_draft(Language::Fr, "some title", "some description", "some content"),
            either::Right(DraftSubmitted {
                aggregate_id: no_post.aggregate_id(),
                title: "some title".to_string(),
                description: "some description".to_string(),
                markdown_content: "some content".to_string(),
                language: Language::Fr,
            })
        );
    }

    #[test]
    fn edit_draft_keeps_public_status() {
        let draft = random_shareable_draft();
        assert_eq!(
            draft.submit_draft(Language::Fr, "some title", "some description", "some content"),
            either::Right(DraftSubmitted {
                aggregate_id: draft.aggregate_id(),
                title: "some title".to_string(),
                description: "some description".to_string(),
                markdown_content: "some content".to_string(),
                language: Language::Fr,
            })
        );
    }

    #[test]
    fn cannot_edit_post_with_draft() {
        let post = random_post();
        assert_eq!(
            post.submit_draft(Language::Fr, "some title", "some description", "some content"),
            either::Left(PostErrors::CannotEditPost)
        );
    }

    #[test]
    fn deleting_a_draft() {
        let draft = random_draft();
        assert_eq!(
            draft.delete_draft(),
            either::Right(DraftDeleted { aggregate_id: draft.aggregate_id() })
        );
    }

    #[test]
    fn cannot_delete_a_post() {
        let post = random_post();
        assert_eq!(
            post.delete_draft(),
            either::Left(PostErrors::CannotDelete)
        );
    }

    #[test]
    fn publish_a_draft() {
        let publication_date = chrono::Utc::now();
        let slug = Slug { slug: rand_str() };
        let draft = random_draft();
        assert_eq!(
            draft.publish_draft(slug.clone(), publication_date),
            either::Right(PostPublished {
                aggregate_id: draft.aggregate_id(),
                slug,
                publication_date,
            })
        );
    }

    #[test]
    fn cannot_publish_a_post() {
        let publication_date = chrono::Utc::now();
        let slug = Slug { slug: rand_str() };
        let post = random_post();
        assert_eq!(
            post.publish_draft(slug.clone(), publication_date),
            either::Left(PostErrors::CannotPublish)
        );
    }

    #[test]
    fn make_draft_public() {
        let draft = random_draft();
        assert_eq!(
            draft.make_public(),
            either::Right(DraftMadePublic { aggregate_id: draft.aggregate_id() })
        );
    }

    #[test]
    fn cannot_make_public_twice() {
        let draft = random_shareable_draft();
        assert_eq!(
            draft.make_public(),
            either::Left(PostErrors::AlreadyPublic)
        );
    }

    #[test]
    fn cannot_make_public_a_post() {
        let post = random_post();
        assert_eq!(
            post.make_public(),
            either::Left(PostErrors::CannotMakePublic)
        );
    }

    #[test]
    fn edit_a_post_will_not_change_title_if_not_necessary() {
        let post = random_post();
        assert_eq!(
            post.edit_post(Language::En, post.title().unwrap(), "other description", "other content"),
            either::Right(PostEdited {
                aggregate_id: post.aggregate_id(),
                title: None,
                description: "other description".to_string(),
                markdown_content: "other content".to_string(),
                language: Language::En,
            })
        );
    }

    #[test]
    fn edit_a_post_changes_the_title_if_necessary() {
        let post = random_post();
        assert_eq!(
            post.edit_post(Language::En, "another title", "other description", "other content"),
            either::Right(PostEdited {
                aggregate_id: post.aggregate_id(),
                title: Some("another title".to_string()),
                description: "other description".to_string(),
                markdown_content: "other content".to_string(),
                language: Language::En,
            })
        );
    }

    #[test]
    fn cannot_edit_draft_as_post() {
        let draft = random_draft();
        assert_eq!(
            draft.edit_post(Language::En, "another title", "other description", "other content"),
            either::Left(PostErrors::CannotEditDraftAsPost)
        );
    }

    #[test]
    fn cannot_perform_any_operation_on_non_existing_expect_submitting_a_draft() {
        let no_post = Post::NonExisting { aggregate_id: rand_str() };
        assert!(no_post.make_public().is_left());
        assert!(no_post.delete_draft().is_left());
        assert!(no_post.publish_draft(Slug { slug: rand_str() }, chrono::Utc::now()).is_left());
        assert!(no_post.edit_post(Language::En, rand_str(), rand_str(), rand_str()).is_left());
    }

    fn rand_str() -> String {
        let mut rng = rand::thread_rng();
        let length_gen = Uniform::from(1..100);
        return thread_rng()
            .sample_iter(&Alphanumeric)
            .take(length_gen.sample(&mut rng))
            .collect();
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
            aggregate_id: rand_str(),
            title: rand_str(),
            description: rand_str(),
            markdown_content: rand_str(),
            language: rand_lang(),
            shareable: false,
        };
    }

    fn random_shareable_draft() -> Post {
        return Post::Draft {
            aggregate_id: rand_str(),
            title: rand_str(),
            description: rand_str(),
            markdown_content: rand_str(),
            language: rand_lang(),
            shareable: true,
        };
    }

    fn random_post() -> Post {
        return Post::Post {
            aggregate_id: rand_str(),
            title: rand_str(),
            description: rand_str(),
            markdown_content: rand_str(),
            language: rand_lang(),
            publication_date: chrono::Utc::now(),
            current_slug: Slug { slug: rand_str() },
            alternative_slugs: Vec::new(),
        };
    }
}
use std::str::FromStr;

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::domain::post::PostEvent::{
    DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostError, PostPublished,
};
use crate::domain::slugify::slugify;
use crate::domain::types::{Language, Markdown, PostId};

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Post {
    NonExisting {
        post_id: PostId,
    },
    Draft {
        post_id: PostId,
        version: u32,
        title: String,
        markdown_content: Markdown,
        language: Language,
        shareable: bool,
    },
    Post {
        post_id: PostId,
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
    pub post_id: PostId,
    pub version: u32,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerPostPublished {
    pub post_id: PostId,
    pub version: u32,
    pub slug: String,
    pub publication_date: DateTime<Utc>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerDraftSubmitted {
    pub post_id: PostId,
    pub version: u32,
    pub title: String,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerPostEdited {
    pub post_id: PostId,
    pub version: u32,
    pub title: Option<String>,
    pub slug: Option<String>,
    pub markdown_content: String,
    pub language: Language,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InnerDraftMadePublic {
    pub post_id: PostId,
    pub version: u32,
}

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct ExportedPost {
    pub post_id: String,
    pub version: u32,
    pub title: String,
    pub markdown_content: String,
    pub language: String,
    pub shareable: bool,
    pub publication_date: Option<String>,
    pub current_slug: Option<String>,
    pub previous_slugs: Vec<String>,
}

impl ExportedPost {
    pub fn import_post(&self) -> Option<Post> {
        Uuid::parse_str(self.post_id.as_str())
            .ok()
            .and_then(|uuid| {
                FromStr::from_str(self.language.as_str())
                    .ok()
                    .map(|l| (uuid, l))
            })
            .map(|(uuid, l)| {
                self.publication_date
                    .clone()
                    .map(|d| {
                        let date_time = DateTime::parse_from_rfc3339(d.as_str())
                            .ok()
                            .map(|d| d.with_timezone(&Utc))
                            .unwrap();
                        Post::Post {
                            post_id: PostId::new(uuid),
                            version: self.version,
                            title: self.title.clone(),
                            markdown_content: Markdown::new(self.markdown_content.clone()),
                            language: l,
                            publication_date: date_time,
                            current_slug: self.current_slug.as_ref().unwrap().clone(),
                            previous_slugs: self.previous_slugs.clone(),
                        }
                    })
                    .unwrap_or(Post::Draft {
                        post_id: PostId::new(uuid),
                        version: self.version,
                        title: self.title.clone(),
                        markdown_content: Markdown::new(self.markdown_content.clone()),
                        language: l,
                        shareable: self.shareable,
                    })
            })
    }
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
        match self {
            PostErrors::CannotDelete => "CannotDelete".to_string(),
            PostErrors::CannotPublish => "CannotPublish".to_string(),
            PostErrors::CannotEditPost => "CannotEditPost".to_string(),
            PostErrors::CannotMakePublic => "CannotMakePublic".to_string(),
            PostErrors::AlreadyPublic => "AlreadyPublic".to_string(),
            PostErrors::CannotEditDraftAsPost => "CannotEditDraftAsPost".to_string(),
            PostErrors::UnknownSlug => "UnknownSlug".to_string(),
            PostErrors::CurrentSlugIsNow(current) => format!("CurrentSlugIsNow({})", current),
        }
    }
}

impl Post {
    pub fn post_id(&self) -> PostId {
        match self {
            Post::NonExisting { post_id } => *post_id,
            Post::Draft { post_id, .. } => *post_id,
            Post::Post { post_id, .. } => *post_id,
        }
    }

    pub fn version(&self) -> u32 {
        match self {
            Post::NonExisting { .. } => 0,
            Post::Draft { version, .. } => *version,
            Post::Post { version, .. } => *version,
        }
    }

    pub fn title(&self) -> Option<String> {
        match self {
            Post::NonExisting { .. } => None,
            Post::Draft { title, .. } => Some(title.clone()),
            Post::Post { title, .. } => Some(title.clone()),
        }
    }

    pub fn check_current_slug(&self, slug: String) -> Result<Self, PostErrors> {
        match self {
            Post::NonExisting { .. } => Ok(self.clone()),
            Post::Draft {
                post_id, shareable, ..
            } => {
                if *shareable && post_id.to_str() == slug {
                    Ok(self.clone())
                } else {
                    Err(PostErrors::UnknownSlug)
                }
            }
            Post::Post {
                current_slug,
                previous_slugs,
                ..
            } => {
                if *current_slug == slug {
                    Ok(self.clone())
                } else if previous_slugs.contains(&slug) {
                    Err(PostErrors::CurrentSlugIsNow(current_slug.clone()))
                } else {
                    Err(PostErrors::UnknownSlug)
                }
            }
        }
    }

    pub fn submit_draft<S: Into<String>, V: Into<String>>(
        &self,
        language: Language,
        title: S,
        markdown_content: V,
    ) -> PostEvent {
        match self {
            Post::Post { .. } => PostError(PostErrors::CannotEditPost),
            _ => DraftSubmitted(InnerDraftSubmitted {
                post_id: self.post_id(),
                version: self.version(),
                title: title.into(),
                markdown_content: markdown_content.into(),
                language,
            }),
        }
    }

    pub fn make_public(&self) -> PostEvent {
        match self {
            Post::Draft {
                shareable: false, ..
            } => DraftMadePublic(InnerDraftMadePublic {
                post_id: self.post_id(),
                version: self.version(),
            }),
            Post::Draft {
                shareable: true, ..
            } => PostError(PostErrors::AlreadyPublic),
            Post::Post { .. } => PostError(PostErrors::CannotMakePublic),
            Post::NonExisting { .. } => PostError(PostErrors::CannotMakePublic),
        }
    }

    pub fn delete_draft(&self) -> PostEvent {
        match self {
            Post::Draft { .. } => DraftDeleted(InnerDraftDeleted {
                post_id: self.post_id(),
                version: self.version(),
            }),
            Post::Post { .. } => PostError(PostErrors::CannotDelete),
            Post::NonExisting { .. } => PostError(PostErrors::CannotDelete),
        }
    }

    pub fn publish_draft(&self, publication_date: DateTime<Utc>) -> PostEvent {
        match self {
            Post::Draft { title, .. } => PostPublished(InnerPostPublished {
                post_id: self.post_id(),
                version: self.version(),
                slug: slugify(title.clone()),
                publication_date,
            }),
            Post::Post { .. } => PostError(PostErrors::CannotPublish),
            Post::NonExisting { .. } => PostError(PostErrors::CannotPublish),
        }
    }

    pub fn edit_post<Title: Into<String>, Content: Into<String>>(
        &self,
        language: Language,
        new_title: Title,
        markdown_content: Content,
    ) -> PostEvent {
        match self {
            Post::Draft { .. } => PostError(PostErrors::CannotEditDraftAsPost),
            Post::Post {
                title,
                current_slug,
                ..
            } => {
                let new_title_as_string = new_title.into();
                let maybe_title_changed = if title.clone() == new_title_as_string {
                    None
                } else {
                    Some(new_title_as_string.clone())
                };
                let maybe_slug_changed = if slugify(new_title_as_string.clone()) == *current_slug {
                    None
                } else {
                    Some(slugify(new_title_as_string))
                };
                PostEdited(InnerPostEdited {
                    post_id: self.post_id(),
                    version: self.version(),
                    language,
                    title: maybe_title_changed,
                    slug: maybe_slug_changed,
                    markdown_content: markdown_content.into(),
                })
            }
            Post::NonExisting { .. } => PostError(PostErrors::CannotEditDraftAsPost),
        }
    }

    pub fn export_post(&self) -> Option<ExportedPost> {
        match self {
            Post::NonExisting { .. } => None,
            Post::Draft {
                post_id,
                version,
                title,
                markdown_content,
                language,
                shareable,
            } => Some(ExportedPost {
                post_id: post_id.to_str(),
                version: *version,
                title: title.clone(),
                markdown_content: markdown_content.to_edit(),
                language: language.to_string(),
                shareable: *shareable,
                publication_date: None,
                current_slug: None,
                previous_slugs: vec![],
            }),
            Post::Post {
                post_id,
                version,
                title,
                markdown_content,
                language,
                publication_date,
                current_slug,
                previous_slugs,
            } => Some(ExportedPost {
                post_id: post_id.to_str(),
                version: *version,
                title: title.clone(),
                markdown_content: markdown_content.to_edit(),
                language: language.to_string(),
                shareable: false,
                publication_date: Some(publication_date.to_rfc3339()),
                current_slug: Some(current_slug.to_string()),
                previous_slugs: previous_slugs.clone(),
            }),
        }
    }
}

#[cfg(test)]
mod test {
    use chrono::{DateTime, NaiveDateTime, Utc};
    use proptest::prelude::*;
    use rand::distributions::Alphanumeric;
    use rand::distributions::Distribution;
    use rand::distributions::Uniform;
    use rand::{thread_rng, Rng};

    use crate::domain::slugify::slugify;
    use crate::domain::types::{Language, Markdown, PostId};

    use super::Post;
    use super::PostErrors;
    use super::PostEvent::{
        DraftDeleted, DraftMadePublic, DraftSubmitted, PostEdited, PostError, PostPublished,
    };
    use super::{
        InnerDraftDeleted, InnerDraftMadePublic, InnerDraftSubmitted, InnerPostEdited,
        InnerPostPublished,
    };

    #[test]
    fn submit_draft_successfully() {
        let no_post = Post::NonExisting {
            post_id: PostId::new(uuid::Uuid::new_v4()),
        };
        assert_eq!(
            no_post.submit_draft(Language::Fr, "some title", "some content"),
            DraftSubmitted(InnerDraftSubmitted {
                post_id: no_post.post_id(),
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
                post_id: draft.post_id(),
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
            DraftDeleted(InnerDraftDeleted {
                post_id: draft.post_id(),
                version: draft.version(),
            })
        );
    }

    #[test]
    fn cannot_delete_a_post() {
        let post = PostBuilder::new().build();
        assert_eq!(post.delete_draft(), PostError(PostErrors::CannotDelete));
    }

    #[test]
    fn publish_a_draft() {
        let publication_date = chrono::Utc::now();
        let draft = random_draft();
        assert_eq!(
            draft.publish_draft(publication_date),
            PostPublished(InnerPostPublished {
                post_id: draft.post_id(),
                version: draft.version(),
                slug: slugify(draft.title().unwrap()),
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
            DraftMadePublic(InnerDraftMadePublic {
                post_id: draft.post_id(),
                version: draft.version(),
            })
        );
    }

    #[test]
    fn cannot_make_public_twice() {
        let draft = random_shareable_draft();
        assert_eq!(draft.make_public(), PostError(PostErrors::AlreadyPublic));
    }

    #[test]
    fn cannot_make_public_a_post() {
        let post = PostBuilder::new().build();
        assert_eq!(post.make_public(), PostError(PostErrors::CannotMakePublic));
    }

    #[test]
    fn edit_a_post_will_not_change_title_if_not_necessary() {
        let post = PostBuilder::new().build();
        assert_eq!(
            post.edit_post(Language::En, post.title().unwrap(), "other content"),
            PostEdited(InnerPostEdited {
                post_id: post.post_id(),
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
                post_id: post.post_id(),
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
        let post = PostBuilder::new().title("What a title!").build();
        assert_eq!(
            post.edit_post(Language::En, "What a title!", "other content"),
            PostEdited(InnerPostEdited {
                post_id: post.post_id(),
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
        let no_post = Post::NonExisting {
            post_id: PostId::new(uuid::Uuid::new_v4()),
        };
        assert!(no_post.make_public().is_err());
        assert!(no_post.delete_draft().is_err());
        assert!(no_post.publish_draft(chrono::Utc::now()).is_err());
        assert!(no_post
            .edit_post(Language::En, rand_str(), rand_str())
            .is_err());
    }

    #[test]
    fn check_current_slug() {
        assert_eq!(
            random_draft().check_current_slug(rand_str()),
            Err(PostErrors::UnknownSlug)
        );
        let draft = random_shareable_draft();
        assert_eq!(
            draft.clone().check_current_slug(rand_str()),
            Err(PostErrors::UnknownSlug)
        );
        assert_eq!(
            draft.clone().check_current_slug(draft.post_id().to_str()),
            Ok(draft.clone())
        );
        let post = PostBuilder::new()
            .with_slug("some-slug")
            .with_old_slugs(&["old-slug", "old-new-slug"])
            .build();
        assert_eq!(
            post.clone().check_current_slug(rand_str()),
            Err(PostErrors::UnknownSlug)
        );
        assert_eq!(
            post.clone().check_current_slug("some-slug".to_string()),
            Ok(post.clone())
        );
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
            post_id: PostId::new(uuid::Uuid::new_v4()),
            version: rand_version(),
            title: rand_str(),
            markdown_content: Markdown::new(rand_str()),
            language: rand_lang(),
            shareable: false,
        };
    }

    fn random_shareable_draft() -> Post {
        return Post::Draft {
            post_id: PostId::new(uuid::Uuid::new_v4()),
            version: rand_version(),
            title: rand_str(),
            markdown_content: Markdown::new(rand_str()),
            language: rand_lang(),
            shareable: true,
        };
    }

    struct PostBuilder {
        post_id: uuid::Uuid,
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
                post_id: uuid::Uuid::new_v4(),
                version: rand_version(),
                title: title.clone(),
                markdown_content: rand_str(),
                language: rand_lang(),
                publication_date: chrono::Utc::now(),
                current_slug: slugify(title.clone()),
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
            self.previous_slugs = slugs.into_iter().map(|s| s.to_string()).collect();
            self
        }

        fn build(&self) -> Post {
            return Post::Post {
                post_id: PostId::new(self.post_id.clone()),
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

    // PROPERTY BASED TESTING FROM HERE

    fn lang_strategy() -> impl Strategy<Value = Language> {
        prop_oneof![Just(Language::Fr), Just(Language::En)]
    }

    fn draft_strategy() -> impl Strategy<Value = Post> {
        (any::<u32>(), ".*", ".*", lang_strategy(), any::<bool>()).prop_map(|(v, t, m, l, sh)| {
            Post::Draft {
                post_id: PostId::new(
                    uuid::Uuid::parse_str("463c7c16-ae78-480f-966a-a118dff12230").unwrap(),
                ),
                version: v,
                title: t,
                markdown_content: Markdown::new(m),
                language: l,
                shareable: sh,
            }
        })
    }

    fn date_strategy() -> impl Strategy<Value = DateTime<Utc>> {
        (0i64..1_000_000_000, 0u32..1_000_000_000)
            .prop_map(|(s, n)| DateTime::from_utc(NaiveDateTime::from_timestamp(s, n), Utc))
    }

    fn slug_strategy() -> impl Strategy<Value = Vec<String>> {
        prop_oneof![
            any::<String>().prop_map(|s| { vec![s] }),
            (any::<String>(), any::<String>(), any::<String>())
                .prop_filter("slug uniqueness", |(s1, s2, s3)| {
                    s1 != s2 && s2 != s3 && s3 != s1
                })
                .prop_map(|(s1, s2, s3)| { vec![s1, s2, s3] })
        ]
    }

    fn post_strategy() -> impl Strategy<Value = Post> {
        (
            any::<u32>(),
            ".*",
            ".*",
            lang_strategy(),
            date_strategy(),
            slug_strategy(),
        )
            .prop_map(|(v, t, m, l, d, sl)| {
                let x = sl.split_first().unwrap();
                Post::Post {
                    post_id: PostId::new(
                        uuid::Uuid::parse_str("463c7c16-ae78-480f-966a-a118dff12230").unwrap(),
                    ),
                    version: v,
                    title: t,
                    markdown_content: Markdown::new(m),
                    language: l,
                    publication_date: d,
                    current_slug: x.0.clone(),
                    previous_slugs: x.1.to_vec(),
                }
            })
    }

    proptest! {
        #[test]
        fn draft_and_exported_drafts_are_equivalent(d in draft_strategy()) {
            prop_assert_eq!(d.clone(), d.export_post().unwrap().import_post().unwrap());
        }

        #[test]
        fn posts_and_exported_posts_are_equivalent(p in post_strategy()) {
            prop_assert_eq!(p.clone(), p.export_post().unwrap().import_post().unwrap());
        }
    }
}

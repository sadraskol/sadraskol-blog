use serde::Deserialize;

#[derive(Deserialize)]
pub struct SubmitDraft {
    pub language: String,
    pub title: String,
    pub markdown_content: String,
}

#[derive(Deserialize)]
pub struct EditPost {
    pub language: String,
    pub title: String,
    pub markdown_content: String,
}

use askama::Template;

#[derive(Template)]
#[template(path = "base.html")]
pub struct BaseTemplate<'a> {
    pub title: &'a str,
}

impl<'a> BaseTemplate<'a> {
    pub fn default() -> BaseTemplate<'a> {
        BaseTemplate { title: "Sadraskol" }
    }
}
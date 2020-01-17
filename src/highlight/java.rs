pub type Code<'a> = Vec<Token<'a>>;

#[derive(PartialEq, Debug, Clone)]
pub enum Token<'a> {
    Literal(&'a str),
    Keyword(&'a str),
}
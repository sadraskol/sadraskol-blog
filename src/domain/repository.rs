use crate::domain::post::{Post, PostEvent};
use crate::domain::types::PostId;

pub trait PostRepository {
    fn all(&mut self) -> Vec<Post>;
    fn all_posts(&mut self) -> Vec<Post>;
    fn all_drafts(&mut self) -> Vec<Post>;
    fn all_archived(&mut self) -> Vec<Post>;
    fn find_by_slug(&mut self, slug: String) -> Option<Post>;
    fn read(&mut self, post_id: PostId) -> Option<Post>;
    fn save(&mut self, event: PostEvent);
    fn upsert(&mut self, post: Post);
}

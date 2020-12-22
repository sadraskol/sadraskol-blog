The goal is to migrate from dynamic to static content.
First because it's  easier to maintain, but also migration is fun!

## Target architecture

Old format is in the database. Two tables:

`blog_posts(aggregate_id, status, language, title, markdown, slug, publication_date, version)`

`blog_slugs(aggregate_id, slug, current)`

For every request to a blog post, the `blog_slugs` table is first queried to find the post or redirect to the current url. Once the current url is fetched, the post with `aggregate_id` is rendered.

This mechanism should remain.

### File hierarchy

In a static layout, redirects and blogs should be present somewhere. A folder contains every accessible blog posts:

```
root/
├── posts
    └── first-post-current-slug
        └── index.html
    └── other-post-with-current-slug
        └── index.html
    └── any-post-with-current-slug
        └── index.html
    └── img
        └── first-image.png
├── index.html
└── redirects
```

In such configuration, file name should remain unique, also no special configuration is required except for the redirection mechanism.

### Redirection Format

For now we use the same format as nginx for redirection: `rewrite`. For example:

```
rewrite /posts/first-post-old-slug /posts/first-post-current-slug permanent;
rewrite /posts/first-post-older-slug /posts/first-post-current-slug permanent;
rewrite /posts/first-post-oldest-slug /posts/first-post-current-slug permanent;
```

We see if we wire it through a CDN next.

### What about shareable drafts?

We drop this functionality for the migration time, draft that are shared are all published. Only the link should remain and will be supported by the redirection format.

## How to migrate?

We want to introduce a new format, one that would remove the need for a postgres database. Redirects are a problem, but post format is also one. We introduce this format before getting to the target architecture, otherwise maintenance of both format will become a hurdle, and remove the will to write other posts :'(

## New format

Post are written with the `sad` file format.

```
root/
├── drafts
    ├── first-draft.sad
    └── img
├── posts
    ├── first-post.sad
    ├── other-post-slug.sad
    ├── any-post.sad
    └── img
        └── first-image.png
└── slugs.sad
```

Posts have the header:

```
title="super"
language="en"
publication_date=1979-05-27T07:32:00-08:00
```

Drafts have no obligation, they remain on the file system of the host and are not deployed.

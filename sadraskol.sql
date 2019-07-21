drop table if exists blog_slugs cascade;
drop table if exists blog_posts cascade;

create table if not exists blog_posts
(
    aggregate_id     uuid not null
        constraint blog_posts_pkey
            primary key,
    status           text,
    language         text not null,
    title            text,
    markdown_content text,
    publication_date timestamp with time zone,
    slug             text,
    version          oid default 0
);

create unique index if not exists blog_posts_aggregate_id_index
    on blog_posts (aggregate_id);

create index if not exists blog_posts_publication_date_index
    on blog_posts (publication_date);

create table if not exists blog_slugs
(
    aggregate_id uuid not null
        references blog_posts (aggregate_id),
    slug         text not null,
    current      bool not null,
    primary key (aggregate_id, slug)
);

create index if not exists blog_slugs_aggregate_id_index
    on blog_slugs (aggregate_id);

create unique index if not exists blog_slugs_slug_index
    on blog_slugs (slug);

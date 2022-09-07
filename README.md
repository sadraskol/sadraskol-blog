# Rust: my rust blog

This code runs my [terrible blog](https://sadraskol.com). I used it to build something with rust.

## Prerequisite

* An updated rust version (runs with `1.43.0` for sure)

## Run the webapp 

In order to run *your* sadraskol blog, follow these steps:

* Write your post in posts/---.sad
* Run `cargo run preview`

You can run `cargo test` for unit tests. 

## Design principle

For this blog I use a single design principle: no javascript, minimal css, maximal bullshit.

This explains the `src/custom_markdown.rs` and `highlight` module which are used to render code
highlighting in the backend. This is a highly inefficient implementation but my blog isn't popular
enough to be a problem.

*note*: This blog is definitely an overkill solution. I advise you to consider
[hugo](https://gohugo.io/) or [Gatsby](https://www.gatsbyjs.com/) if you want to run
a proper blog.

## LICENSE

This code uses a modified version of [pulldown_cmark](https://github.com/raphlinus/pulldown-cmark/)
under [MIT License](https://opensource.org/licenses/MIT): Copyright 2015 Google Inc. All rights reserved.

Copyright 2020 Thomas Bracher. All rights reserved.  
This work is available under [MIT License](https://opensource.org/licenses/MIT)

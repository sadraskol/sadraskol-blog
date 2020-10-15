# Rust: my rust blog

This code runs my [terrible blog](https://sadraskol.com). I used it to build something with rust.

## Prerequisite

* You need a postgres database with `sadraskol.sql` schema
* An updated rust version (runs with `1.43.0` for sure)
* Docker (optional)

## Run the webapp 

In order to run *your* sadraskol blog, follow these steps:

* Create your `config/dev.toml` (defined by `src/config.rs`) with the correct postgres connection url:

``` toml
host = "localhost"
port = 4000
cookie_seed = "1N8nZYVIDjye5ezQDojzkxJDi0801ow48PqUmFmKzQUoznIunwrws2fzY1B7usD1"

[postgres]
url = "host=localhost port=5432 user=postgres password=postgres connect_timeout=4 dbname=sadraskol_dev"

[admin]
login = "admin"
password = "password"
```

* Run `cargo run`
* Connect to `localhost:4000/login` with the configured admin login
* Write your first blog post

## Tests

You can run `cargo test` for unit tests and `cargo run --bin integration_tests` for
integration tests against a postgres instance in a docker container. 

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

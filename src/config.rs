use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize)]
pub struct Config {
    pub host: String,
    pub port: u16,
    pub cookie_seed: String,
    pub postgres: Postgres,
    pub admin: Admin,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Admin {
    pub login: String,
    pub password: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Postgres {
    pub url: String,
}

pub fn cfg() -> Config {
    let cfg_path = if cfg!(feature = "production") {
        "config/prod.toml"
    } else {
        "config/dev.toml"
    };
    let file_content = std::fs::read_to_string(std::path::PathBuf::from(cfg_path))
        .unwrap_or_else(|_| panic!("could not access {}", cfg_path));
    toml::from_str(file_content.as_str()).expect("Could not deserialize from file content")
}

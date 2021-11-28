use std::fs;
use std::io::{Read, Write};
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::domain::date::Date;
use crate::domain::types::{Markdown, SadPost};

pub struct FileDiff {
    r: fs::File,
    w: fs::File,
    original_len: usize,
}

impl FileDiff {
    pub fn new<T: ToString>(path: T) -> Self {
        let string = path.to_string();
        let p = Path::new(string.as_str());

        if let Some(parent) = p.parent() {
            fs::create_dir_all(parent).unwrap();
        }

        if p.is_dir() {
            fs::remove_dir_all(p).unwrap();
        }

        let w = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .open(p)
            .unwrap();

        let file = fs::OpenOptions::new().read(true).open(p).unwrap();

        let len = file.metadata().unwrap().len() as usize;
        FileDiff {
            r: file,
            original_len: len,
            w,
        }
    }

    pub fn write_diff<T: ToString>(&mut self, content: T) {
        let mut original = String::with_capacity(self.original_len);
        self.r.read_to_string(&mut original).unwrap();
        let content_as_string = content.to_string();
        if original != content_as_string {
            self.w.set_len(content_as_string.len() as u64).unwrap();
            self.w.write_all(content_as_string.as_bytes()).unwrap();
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct SadHeader {
    title: String,
    language: String,
    publication_date: String,
    image: Option<String>,
}

pub fn read_post(path: &Path) -> SadPost {
    let s = fs::read_to_string(path).unwrap();
    let v: Vec<_> = s.split("---- sadraskol ----").collect();
    let header: SadHeader = toml::from_str(v[0]).unwrap();
    let content = v[1];

    let date_time = Date::parse_from_rfc3339(header.publication_date.as_str()).unwrap();

    SadPost {
        title: header.title,
        language: header.language,
        publication_date: date_time,
        saddown_content: Markdown::new(content),
        image: header.image,
    }
}

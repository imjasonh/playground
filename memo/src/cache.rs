//! The on-disk cache. Each key has its own directory with up to
//! [`KEEP`] entries, newest first, and a note about the last run.
//!
//! An entry is a JSON manifest (`ID.json`) and the recorded output
//! (`ID.out`). The output is renamed into place before the manifest, and
//! readers only look at manifests, so a reader never sees half an entry.

use crate::record::PathExpect;
use serde::{Deserialize, Serialize};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};

/// Entries kept per key. Several let a result survive switching back and
/// forth between two states of the inputs, such as two git branches.
pub const KEEP: usize = 4;

const VERSION: u32 = 1;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Entry {
    pub version: u32,
    pub created_ms: i64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expires_ms: Option<i64>,
    pub argv: Vec<String>,
    pub cwd: String,
    pub exit_code: i32,
    pub duration_ms: u64,
    pub paths: Vec<PathExpect>,
    /// Network access that was allowed because the entry expires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub net: Vec<String>,
}

/// What happened the last time a key's command ran.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LastRun {
    pub at_ms: i64,
    pub exit_code: i32,
    pub cached: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reasons: Vec<String>,
}

pub struct Store {
    root: PathBuf,
}

/// Returns `$MEMO_CACHE_DIR`, or `memo` under `$XDG_CACHE_HOME` or
/// `~/.cache`.
pub fn default_dir() -> Option<PathBuf> {
    if let Some(d) = std::env::var_os("MEMO_CACHE_DIR").filter(|d| !d.is_empty()) {
        return Some(PathBuf::from(d));
    }
    if let Some(d) = std::env::var_os("XDG_CACHE_HOME").filter(|d| !d.is_empty()) {
        return Some(PathBuf::from(d).join("memo"));
    }
    std::env::var_os("HOME")
        .filter(|d| !d.is_empty())
        .map(|h| PathBuf::from(h).join(".cache").join("memo"))
}

fn write_private(path: &Path, data: &[u8]) -> io::Result<()> {
    static SEQ: AtomicU32 = AtomicU32::new(0);
    let tmp = path.with_extension(format!(
        "tmp{}-{}",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    let mut f = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&tmp)?;
    f.write_all(data)?;
    drop(f);
    fs::rename(&tmp, path).inspect_err(|_| {
        let _ = fs::remove_file(&tmp);
    })
}

impl Store {
    /// Opens the cache in `root`, creating it with mode 0700.
    pub fn open(root: PathBuf) -> io::Result<Store> {
        DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(root.join("v1"))?;
        Ok(Store { root })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    fn dir(&self, key: &str) -> PathBuf {
        self.root.join("v1").join(key)
    }

    /// Returns the IDs of the entries for `key`, newest first. An ID starts
    /// with its creation time, so this reads no manifests.
    pub fn ids(&self, key: &str) -> Vec<String> {
        let Ok(rd) = fs::read_dir(self.dir(key)) else {
            return Vec::new();
        };
        let mut ids: Vec<(i64, String)> = rd
            .filter_map(|e| {
                let name = e.ok()?.file_name().into_string().ok()?;
                let id = name.strip_suffix(".json")?;
                let created: i64 = id.split('-').next()?.parse().ok()?;
                Some((created, id.to_string()))
            })
            .collect();
        ids.sort_by(|a, b| b.cmp(a));
        ids.into_iter().map(|(_, id)| id).collect()
    }

    pub fn load(&self, key: &str, id: &str) -> Option<Entry> {
        let data = fs::read(self.dir(key).join(format!("{id}.json"))).ok()?;
        let entry: Entry = serde_json::from_slice(&data).ok()?;
        (entry.version == VERSION).then_some(entry)
    }

    /// Returns every entry for `key`, newest first, with its ID.
    pub fn entries(&self, key: &str) -> Vec<(String, Entry)> {
        self.ids(key)
            .into_iter()
            .filter_map(|id| self.load(key, &id).map(|e| (id, e)))
            .collect()
    }

    pub fn output(&self, key: &str, id: &str) -> io::Result<Vec<u8>> {
        fs::read(self.dir(key).join(format!("{id}.out")))
    }

    /// Saves an entry and its encoded output, then drops entries beyond
    /// [`KEEP`].
    pub fn save(&self, key: &str, entry: &Entry, output: &[u8]) -> io::Result<()> {
        let dir = self.dir(key);
        DirBuilder::new().recursive(true).mode(0o700).create(&dir)?;
        let id = format!("{}-{}", entry.created_ms, std::process::id());
        write_private(&dir.join(format!("{id}.out")), output)?;
        let json = serde_json::to_vec(entry).map_err(io::Error::other)?;
        write_private(&dir.join(format!("{id}.json")), &json)?;
        for old in self.ids(key).into_iter().skip(KEEP) {
            let _ = fs::remove_file(dir.join(format!("{old}.json")));
            let _ = fs::remove_file(dir.join(format!("{old}.out")));
        }
        Ok(())
    }

    pub fn save_last(&self, key: &str, last: &LastRun) -> io::Result<()> {
        let dir = self.dir(key);
        DirBuilder::new().recursive(true).mode(0o700).create(&dir)?;
        let json = serde_json::to_vec(last).map_err(io::Error::other)?;
        write_private(&dir.join("last.json"), &json)
    }

    pub fn last(&self, key: &str) -> Option<LastRun> {
        serde_json::from_slice(&fs::read(self.dir(key).join("last.json")).ok()?).ok()
    }

    /// Deletes every cached result.
    pub fn clear(&self) -> io::Result<()> {
        match fs::remove_dir_all(self.root.join("v1")) {
            Err(e) if e.kind() != io::ErrorKind::NotFound => Err(e),
            _ => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(created_ms: i64) -> Entry {
        Entry {
            version: VERSION,
            created_ms,
            expires_ms: None,
            argv: vec!["true".into()],
            cwd: "/".into(),
            exit_code: 0,
            duration_ms: 1,
            paths: vec![],
            net: vec![],
        }
    }

    #[test]
    fn keeps_the_newest_entries() {
        let dir = tempfile::tempdir().unwrap();
        let store = Store::open(dir.path().join("cache")).unwrap();
        for t in 0..6 {
            store.save("k", &entry(t), &[t as u8]).unwrap();
        }
        let got = store.entries("k");
        assert_eq!(got.len(), KEEP);
        assert_eq!(got[0].1.created_ms, 5);
        assert_eq!(store.output("k", &got[0].0).unwrap(), vec![5]);
        assert!(store.entries("other").is_empty());
        store
            .save_last(
                "k",
                &LastRun {
                    at_ms: 9,
                    ..LastRun::default()
                },
            )
            .unwrap();
        assert_eq!(store.last("k").unwrap().at_ms, 9);
        assert_eq!(store.entries("k").len(), KEEP);
        store.clear().unwrap();
        assert!(store.entries("k").is_empty());
    }
}

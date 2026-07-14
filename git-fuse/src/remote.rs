//! Client for git-server's JSON read API.
//!
//! Only the three read endpoints the filesystem needs:
//!
//! * `GET /api/<repo>/refs` — ref name → oid map plus the HEAD symref;
//! * `GET /api/<repo>/tree/<refish>/<path>` — one directory listing;
//! * `GET /api/<repo>/file/<refish>/<path>` — raw blob bytes.
//!
//! These answer in one HTTP round-trip with no pack transfer, which is what
//! makes cold reads fast while the local cache is still warming.

use serde::Deserialize;
use std::collections::BTreeMap;
use std::io::Read;
use std::time::Duration;

/// Remote read cap. `/api/file` streams whole blobs; a runaway response
/// should fail rather than exhaust memory.
const MAX_BLOB_BYTES: u64 = 1 << 30;

pub(crate) struct Remote {
    agent: ureq::Agent,
    /// `…/api/<repo>` with no trailing slash.
    api_base: String,
}

#[derive(Debug, Deserialize)]
pub(crate) struct RefsResponse {
    /// HEAD's symref target (e.g. `refs/heads/main`).
    pub head: String,
    /// Full ref name → hex oid. BTreeMap keeps listings sorted.
    pub refs: BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct TreeResponse {
    pub entries: Vec<TreeEntry>,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct TreeEntry {
    pub name: String,
    /// Octal string as git prints it: `100644`, `100755`, `120000`, `40000`.
    pub mode: String,
    /// `"blob"` or `"tree"`.
    pub kind: String,
    pub oid: String,
    /// Blob size; absent for trees.
    pub size: Option<u64>,
}

impl Remote {
    /// `remote_url` is the clone URL (`https://host/<repo>`); the API base is
    /// the same host with `/api` inserted before the repo segment.
    pub(crate) fn new(remote_url: &str) -> Result<Remote, String> {
        let url = remote_url.trim_end_matches('/');
        let url = url.strip_suffix(".git").unwrap_or(url);
        let (base, repo) = url
            .rsplit_once('/')
            .ok_or_else(|| format!("bad remote url {remote_url}"))?;
        if repo.is_empty() || !base.contains("://") {
            return Err(format!("bad remote url {remote_url}"));
        }
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            .timeout(Duration::from_secs(60))
            .build();
        Ok(Remote {
            agent,
            api_base: format!("{base}/api/{repo}"),
        })
    }

    pub(crate) fn refs(&self) -> Result<RefsResponse, String> {
        let resp = self
            .agent
            .get(&format!("{}/refs", self.api_base))
            .call()
            .map_err(|e| format!("refs: {e}"))?;
        resp.into_json().map_err(|e| format!("refs: {e}"))
    }

    /// List a directory. `Ok(None)` when the path isn't a directory at that
    /// commit (or the refish is unknown).
    pub(crate) fn tree(&self, refish: &str, path: &str) -> Result<Option<TreeResponse>, String> {
        let url = format!("{}/tree/{refish}/{}", self.api_base, encode_path(path));
        match self.agent.get(&url).call() {
            Ok(resp) => resp
                .into_json()
                .map(Some)
                .map_err(|e| format!("tree {refish}/{path}: {e}")),
            Err(ureq::Error::Status(404, _)) => Ok(None),
            Err(e) => Err(format!("tree {refish}/{path}: {e}")),
        }
    }

    /// Fetch a file's raw contents. `Ok(None)` when the path is absent or a
    /// directory.
    pub(crate) fn file(&self, refish: &str, path: &str) -> Result<Option<Vec<u8>>, String> {
        let url = format!("{}/file/{refish}/{}", self.api_base, encode_path(path));
        match self.agent.get(&url).call() {
            Ok(resp) => {
                let mut data = Vec::new();
                resp.into_reader()
                    .take(MAX_BLOB_BYTES)
                    .read_to_end(&mut data)
                    .map_err(|e| format!("file {refish}/{path}: {e}"))?;
                Ok(Some(data))
            }
            Err(ureq::Error::Status(404, _)) => Ok(None),
            Err(e) => Err(format!("file {refish}/{path}: {e}")),
        }
    }
}

/// Percent-encode the characters that would change URL interpretation while
/// leaving `/` separators intact (the server splits on them).
fn encode_path(path: &str) -> String {
    let mut out = String::with_capacity(path.len());
    for b in path.bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' => out.push(b as char),
            b'/' | b'-' | b'_' | b'.' | b'~' => out.push(b as char),
            _ => out.push_str(&format!("%{b:02X}")),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn api_base_derivation() {
        for url in [
            "http://localhost:8080/myrepo",
            "http://localhost:8080/myrepo/",
            "http://localhost:8080/myrepo.git",
        ] {
            let r = Remote::new(url).unwrap();
            assert_eq!(r.api_base, "http://localhost:8080/api/myrepo");
        }
        assert!(Remote::new("nonsense").is_err());
    }

    #[test]
    fn path_encoding() {
        assert_eq!(encode_path("a/b c.txt"), "a/b%20c.txt");
        assert_eq!(encode_path("plain/path.rs"), "plain/path.rs");
    }
}

//! Parse the Worker's `GET /` catalog JSON.

use serde::Deserialize;

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Catalog {
    pub revision: u64,
    pub latest: Option<String>,
    pub images: Vec<String>,
}

impl Catalog {
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        serde_json::from_slice(bytes).map_err(|e| e.to_string())
    }

    /// Pick a rotation target: prefer a different image than `current`.
    pub fn pick_random(&self, current: Option<&str>, rand_u32: u32) -> Option<&str> {
        if self.images.is_empty() {
            return None;
        }
        if self.images.len() == 1 {
            return self.images.first().map(String::as_str);
        }
        let mut choices: Vec<&str> = self
            .images
            .iter()
            .map(String::as_str)
            .filter(|n| Some(*n) != current)
            .collect();
        if choices.is_empty() {
            choices = self.images.iter().map(String::as_str).collect();
        }
        let idx = (rand_u32 as usize) % choices.len();
        Some(choices[idx])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_catalog() {
        let c = Catalog::parse(br#"{"revision":3,"latest":"foo","images":["bar","foo"]}"#).unwrap();
        assert_eq!(c.revision, 3);
        assert_eq!(c.latest.as_deref(), Some("foo"));
        assert_eq!(c.images, vec!["bar", "foo"]);
    }

    #[test]
    fn pick_random_avoids_current() {
        let c = Catalog {
            revision: 1,
            latest: Some("a".into()),
            images: vec!["a".into(), "b".into(), "c".into()],
        };
        for r in 0..20 {
            let pick = c.pick_random(Some("a"), r).unwrap();
            assert_ne!(pick, "a");
        }
    }
}

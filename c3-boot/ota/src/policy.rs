//! Reads the release identity policy from a file.
//!
//! A policy file holds one `name=value` line for each of the five fields,
//! in any order. Blank lines and lines that start with `#` are ignored.
//! The bootloader's build script reads the same format.

/// The field names, in the order of [`c3_verify::trustroot::Policy`].
pub const NAMES: [&str; 5] = [
    "issuer",
    "build-signer-uri",
    "repository-id",
    "owner-id",
    "trigger",
];

/// Parses a policy file into issuer, Build Signer URI, repository ID, owner
/// ID, and trigger.
pub fn parse(text: &str) -> Result<[String; 5], String> {
    let mut out: [Option<String>; 5] = Default::default();
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (name, value) = line
            .split_once('=')
            .ok_or_else(|| format!("policy line {line:?} isn't name=value"))?;
        let i = NAMES
            .iter()
            .position(|n| *n == name)
            .ok_or_else(|| format!("unknown policy field {name}"))?;
        if out[i].replace(value.to_string()).is_some() {
            return Err(format!("policy field {name} appears twice"));
        }
    }
    let mut fields = out.into_iter().zip(NAMES);
    let mut next = || -> Result<String, String> {
        let (value, name) = fields.next().ok_or("too few fields")?;
        value.ok_or_else(|| format!("policy has no {name}"))
    };
    Ok([next()?, next()?, next()?, next()?, next()?])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_committed_policies() {
        for text in [
            include_str!("../../release/policy"),
            include_str!("../../testdata/keys/dev-policy"),
        ] {
            let p = parse(text).unwrap();
            assert_eq!(p[0], "https://token.actions.githubusercontent.com");
            assert_eq!(p[4], "push");
        }
    }

    #[test]
    fn rejects_missing_unknown_and_repeated_fields() {
        let full = "issuer=a\nbuild-signer-uri=b\nrepository-id=1\nowner-id=2\ntrigger=push\n";
        assert!(parse(full).is_ok());
        assert!(parse(&full.replace("trigger=push\n", "")).is_err());
        assert!(parse(&format!("{full}issuer=c\n")).is_err());
        assert!(parse(&format!("{full}color=red\n")).is_err());
        assert!(parse(&format!("{full}junk\n")).is_err());
    }
}

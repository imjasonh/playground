//! Source-level include preprocessor.
//!
//! Before lexing, scan the source for `include "path"` directives at the
//! start of lines and splice in the contents of those files. Tracks an
//! include stack to detect circular includes.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Preprocess a source file, inlining all `include "path"` directives.
pub fn preprocess(source: &str, source_path: Option<&Path>) -> Result<String, String> {
    let mut visited = HashSet::new();
    let base_dir = source_path
        .and_then(|p| p.parent())
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    if let Some(p) = source_path {
        if let Ok(canon) = p.canonicalize() {
            visited.insert(canon);
        }
    }
    process(source, &base_dir, &mut visited)
}

fn process(
    source: &str,
    base_dir: &Path,
    visited: &mut HashSet<PathBuf>,
) -> Result<String, String> {
    let mut out = String::new();
    for line in source.lines() {
        if let Some(path_str) = parse_include_line(line) {
            let include_path = resolve_include(base_dir, path_str);
            let canon = include_path
                .canonicalize()
                .map_err(|e| format!("failed to open '{}': {e}", include_path.display()))?;
            if !visited.insert(canon.clone()) {
                return Err(format!(
                    "circular include: '{}' is already in the include stack",
                    include_path.display()
                ));
            }
            let included = std::fs::read_to_string(&canon)
                .map_err(|e| format!("failed to read '{}': {e}", canon.display()))?;
            // Use the included file's directory as base for its own includes
            let nested_base = canon
                .parent()
                .map_or_else(|| base_dir.to_path_buf(), std::path::Path::to_path_buf);
            let processed = process(&included, &nested_base, visited)?;
            out.push_str(&processed);
            out.push('\n');
            // Remove from visited so siblings can re-include (only cycles
            // through the current branch are forbidden).
            visited.remove(&canon);
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    Ok(out)
}

/// Parse a line like `include "path/to/file.ne"` and extract the path.
/// Returns None if the line is not an include directive.
fn parse_include_line(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    let rest = trimmed.strip_prefix("include")?;
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    Some(&rest[..end])
}

fn resolve_include(base_dir: &Path, path_str: &str) -> PathBuf {
    let p = Path::new(path_str);
    if p.is_absolute() {
        p.to_path_buf()
    } else {
        base_dir.join(p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preprocess_no_includes_passthrough() {
        let src = "game \"T\" { mapper: NROM }\non frame { wait_frame }\nstart Main\n";
        let out = preprocess(src, None).unwrap();
        assert!(out.contains("game \"T\""));
    }

    #[test]
    fn parse_include_line_valid() {
        assert_eq!(parse_include_line("include \"foo.ne\""), Some("foo.ne"));
        assert_eq!(parse_include_line("  include \"a/b.ne\""), Some("a/b.ne"));
    }

    #[test]
    fn parse_include_line_invalid() {
        assert_eq!(parse_include_line("var x: u8 = 0"), None);
        assert_eq!(parse_include_line("include foo.ne"), None); // no quotes
        assert_eq!(parse_include_line("// include \"foo.ne\""), None);
    }

    #[test]
    fn preprocess_with_temp_file() {
        use std::io::Write;
        let dir = std::env::temp_dir();
        let inc_path = dir.join("nescript_test_include.ne");
        let main_path = dir.join("nescript_test_main.ne");

        std::fs::write(&inc_path, "const SPEED: u8 = 5\n").unwrap();
        let main_src = format!("include \"{}\"\nvar x: u8 = 0\n", inc_path.display());
        let mut f = std::fs::File::create(&main_path).unwrap();
        f.write_all(main_src.as_bytes()).unwrap();

        let out = preprocess(&main_src, Some(&main_path)).unwrap();
        assert!(out.contains("const SPEED"));
        assert!(out.contains("var x: u8"));

        let _ = std::fs::remove_file(&inc_path);
        let _ = std::fs::remove_file(&main_path);
    }
}

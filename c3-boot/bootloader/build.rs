//! Links the bootloader with its memory layout and compiles in the pinned
//! TUF root and the release identity policy.

use std::env;
use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

/// The policy fields, in the order of `c3_verify::trustroot::Policy`, with
/// the names a policy file uses for them.
const FIELDS: [(&str, &str); 5] = [
    ("issuer", "ISSUER"),
    ("build-signer-uri", "BUILD_SIGNER_URI"),
    ("repository-id", "REPOSITORY_ID"),
    ("owner-id", "OWNER_ID"),
    ("trigger", "TRIGGER"),
];

/// Reads a policy file: one `name=value` line for each field, in any order,
/// with blank lines and `#` comments ignored. `c3-ota` reads the same
/// format.
fn read_policy(text: &str) -> [String; 5] {
    let mut out: [Option<String>; 5] = Default::default();
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (name, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("policy line {line:?} isn't name=value"));
        let i = FIELDS
            .iter()
            .position(|(n, _)| *n == name)
            .unwrap_or_else(|| panic!("unknown policy field {name}"));
        assert!(
            value.bytes().all(|b| b.is_ascii_graphic()),
            "policy field {name} isn't printable ASCII"
        );
        assert!(
            out[i].replace(value.to_string()).is_none(),
            "policy field {name} appears twice"
        );
    }
    let mut i = 0;
    out.map(|v| {
        let name = FIELDS[i].0;
        i += 1;
        v.unwrap_or_else(|| panic!("policy has no {name}"))
    })
}

fn main() {
    let dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));
    let workspace = dir.join("..");
    println!("cargo:rustc-link-search={}", dir.display());
    println!("cargo:rustc-link-arg-bins=-Tbootloader.x");
    println!("cargo:rustc-link-arg-bins=-Trom.x");
    println!("cargo:rerun-if-changed=rom.x");
    println!("cargo:rerun-if-changed=bootloader.x");

    // The c3_* cfgs choose what the bootloader may do to a device, so only
    // this script may set them, from C3_TUF_ROOT and C3_EFUSE_BURN.
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    let flags = env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    assert!(
        !flags.split('\u{1f}').any(|f| f.contains("c3_")),
        "set c3-boot's build options with C3_TUF_ROOT, C3_POLICY, and C3_EFUSE_BURN, not RUSTFLAGS"
    );

    // C3_TUF_ROOT names the canonical root that `c3-ota tuf-root` writes.
    // Relative paths here and in C3_POLICY start at the workspace, c3-boot.
    // There is no default: the development repository's seeds are public,
    // so a build must ask for it by name with C3_TUF_ROOT=dev, and that
    // build warns on every boot.
    println!("cargo:rerun-if-env-changed=C3_TUF_ROOT");
    let choice = env::var("C3_TUF_ROOT").expect(
        "set C3_TUF_ROOT to a canonical Sigstore root, or to `dev` for the public development root",
    );
    let dev = choice == "dev";
    let root_path = if dev {
        workspace.join("testdata/keys/tuf-dev-root.json")
    } else {
        workspace.join(choice)
    };
    if dev {
        println!("cargo:rustc-cfg=c3_dev_root");
    }
    println!("cargo:rustc-check-cfg=cfg(c3_dev_root)");

    // C3_POLICY names a policy file. It defaults to fakestore's identity for
    // the development root and to c3-release.yml on main otherwise.
    println!("cargo:rerun-if-env-changed=C3_POLICY");
    let policy_path = match env::var("C3_POLICY") {
        Ok(p) => workspace.join(p),
        Err(_) if dev => workspace.join("testdata/keys/dev-policy"),
        Err(_) => workspace.join("release/policy"),
    };

    // C3_EFUSE_BURN=on lets the bootloader program SECURE_VERSION, which
    // can't be undone. Without it, the bootloader logs the raise it would
    // have made and boots anyway, so test boards keep every level. Builds
    // with a production root must burn.
    println!("cargo:rerun-if-env-changed=C3_EFUSE_BURN");
    let burn = match env::var("C3_EFUSE_BURN").as_deref() {
        Ok("on") => true,
        Ok("off") | Err(_) => false,
        Ok(other) => panic!("C3_EFUSE_BURN must be `on` or `off`, not `{other}`"),
    };
    assert!(
        dev || burn,
        "a bootloader with a production TUF root needs C3_EFUSE_BURN=on"
    );
    if burn {
        println!("cargo:rustc-cfg=c3_efuse_burn");
    }
    println!("cargo:rustc-check-cfg=cfg(c3_efuse_burn)");

    println!("cargo:rerun-if-changed={}", root_path.display());
    let root = fs::read(&root_path).expect("the TUF root is readable");
    if let Err(e) = c3_verify::tuf::parse_root(&root) {
        panic!(
            "{} isn't a canonical TUF root ({e:?}); write it with `c3-ota tuf-root`",
            root_path.display()
        );
    }
    println!("cargo:rerun-if-changed={}", policy_path.display());
    let policy = read_policy(&fs::read_to_string(&policy_path).expect("the policy is readable"));

    let out = PathBuf::from(env::var("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let root_copy = out.join("root.json");
    fs::write(&root_copy, &root).expect("OUT_DIR is writable");
    let mut code = format!(
        "#[unsafe(link_section = \".rodata_boot\")]\n\
         pub static ROOT: [u8; {}] = *include_bytes!({:?});\n",
        root.len(),
        root_copy.display().to_string()
    );
    for ((_, name), value) in FIELDS.iter().zip(&policy) {
        let _ = writeln!(
            code,
            "#[unsafe(link_section = \".rodata_boot\")]\n\
             static {name}: [u8; {}] = *b{value:?};",
            value.len()
        );
    }
    code.push_str("pub const POLICY: Policy<'static> = Policy {\n");
    for (field, name) in FIELDS {
        let _ = writeln!(code, "    {}: &{name},", field.replace('-', "_"));
    }
    code.push_str("};\n");
    fs::write(out.join("pinned.rs"), code).expect("OUT_DIR is writable");
}

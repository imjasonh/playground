//! `c3-ota`: build, sign, and check c3-boot slots.
//!
//! Run `c3-ota help` for the subcommands.

use std::collections::HashMap;
use std::fs;
use std::process::ExitCode;

use std::path::Path;

use c3_ota::container;
use c3_ota::image;
use c3_ota::slot;
use c3_ota::trusted;
use c3_ota::tuf;
use c3_verify::bootstate;

const USAGE: &str = "usage: c3-ota <command> [--flag value]...

commands:
  pack --elf FILE --security-version N --out FILE
  bootloader-image --elf FILE --out FILE
  container --bundle FILE [--image FILE] --out FILE
  describe --trusted-root FILE               print what a device would trust
  slot --image FILE --bundle FILE --tuf FILE --out FILE
  verify --slot FILE --pinned FILE POLICY [--level N]
  record --preferred a|b [--trial a|b --boots N] [--confirmed a,b]
         [--generation N] --out FILE
  flash --bootloader FILE [--record FILE] [--slot-a FILE] [--slot-b FILE] --out FILE
  tuf-root --root FILE --out FILE            canonical root to pin in the bootloader
  tuf-package [--roots FILE,FILE] --targets FILE --trusted-root FILE --out FILE
  tuf-verify --pinned FILE --tuf FILE
  tuf-accept --image FILE --bundle FILE --tuf FILE --pinned FILE POLICY
             [--level N]
  tuf-dev-root --keys DIR --version N --out FILE
  tuf-dev-targets --keys DIR --root-version N --trusted-root FILE
                  [--expires TIME] --out FILE

POLICY is --policy FILE, or --issuer S --build-signer-uri S
--repository-id S --owner-id S --trigger S.";

struct Args {
    flags: HashMap<String, String>,
}

impl Args {
    fn parse(rest: &[String]) -> Result<Self, String> {
        let mut flags = HashMap::new();
        let mut it = rest.iter();
        while let Some(flag) = it.next() {
            let name = flag
                .strip_prefix("--")
                .ok_or_else(|| format!("expected a flag, got {flag}"))?;
            let value = it.next().ok_or_else(|| format!("--{name} needs a value"))?;
            flags.insert(name.to_string(), value.clone());
        }
        Ok(Args { flags })
    }

    fn get(&self, name: &str) -> Result<&str, String> {
        self.flags
            .get(name)
            .map(String::as_str)
            .ok_or_else(|| format!("missing --{name}"))
    }

    fn opt(&self, name: &str) -> Option<&str> {
        self.flags.get(name).map(String::as_str)
    }

    fn read(&self, name: &str) -> Result<Vec<u8>, String> {
        let path = self.get(name)?;
        fs::read(path).map_err(|e| format!("{path}: {e}"))
    }

    fn number<T: std::str::FromStr>(&self, name: &str) -> Result<T, String> {
        self.get(name)?
            .parse()
            .map_err(|_| format!("--{name} isn't a number"))
    }

    fn write(&self, bytes: &[u8]) -> Result<(), String> {
        let path = self.get("out")?;
        fs::write(path, bytes).map_err(|e| format!("{path}: {e}"))
    }
}

fn policy(a: &Args) -> Result<[String; 5], String> {
    if a.opt("policy").is_some() {
        let text = String::from_utf8(a.read("policy")?).map_err(|e| e.to_string())?;
        return c3_ota::policy::parse(&text);
    }
    let [i, b, r, o, t] = c3_ota::policy::NAMES.map(|n| a.get(n).map(str::to_string));
    Ok([i?, b?, r?, o?, t?])
}

fn level(a: &Args) -> Result<u8, String> {
    if a.opt("level").is_some() {
        a.number("level")
    } else {
        Ok(0)
    }
}

fn slot_name(text: &str) -> Result<bootstate::Slot, String> {
    match text {
        "a" => Ok(bootstate::Slot::A),
        "b" => Ok(bootstate::Slot::B),
        _ => Err(format!("slot must be a or b, not {text}")),
    }
}

fn run(command: &str, a: &Args) -> Result<(), String> {
    match command {
        "pack" => a.write(&image::pack(
            &a.read("elf")?,
            a.number("security-version")?,
        )?),
        "bootloader-image" => a.write(&image::esp_image(&a.read("elf")?)?),
        "container" => {
            let json = String::from_utf8(a.read("bundle")?).map_err(|e| e.to_string())?;
            let digest = match a.opt("image") {
                Some(_) => Some(c3_crypto::sha256(&a.read("image")?)),
                None => None,
            };
            a.write(&container::from_bundle_json(&json, digest.as_ref())?)
        }
        "describe" => {
            let json = String::from_utf8(a.read("trusted-root")?).map_err(|e| e.to_string())?;
            let spec = trusted::TrustRootSpec::from_trusted_root(&json, Default::default())?;
            print!("{}", spec.describe()?);
            Ok(())
        }
        "slot" => a.write(&slot::assemble(
            &a.read("image")?,
            &a.read("bundle")?,
            &a.read("tuf")?,
        )?),
        "verify" => {
            let accepted =
                slot::verify(&a.read("slot")?, &a.read("pinned")?, &policy(a)?, level(a)?)?;
            println!(
                "accepted: level {}, entry {:#x}, signed at {}",
                accepted.level, accepted.header.entry_point, accepted.signed_time
            );
            Ok(())
        }
        "record" => {
            let trial = match a.opt("trial") {
                Some(t) => Some(bootstate::Trial {
                    slot: slot_name(t)?,
                    boots_left: a.number("boots")?,
                }),
                None => None,
            };
            let mut state = bootstate::State::DEFAULT;
            state.preferred = slot_name(a.get("preferred")?)?;
            state.trial = trial;
            state.generation = if a.opt("generation").is_some() {
                a.number("generation")?
            } else {
                1
            };
            if let Some(list) = a.opt("confirmed") {
                for s in list.split(',') {
                    state = state.with_confirmed(slot_name(s)?);
                }
            }
            a.write(&bootstate::encode(&state))
        }
        "flash" => {
            let opt = |name: &str| -> Result<Option<Vec<u8>>, String> {
                match a.opt(name) {
                    Some(_) => a.read(name).map(Some),
                    None => Ok(None),
                }
            };
            let (record, sa, sb) = (opt("record")?, opt("slot-a")?, opt("slot-b")?);
            a.write(&slot::flash_image(
                &a.read("bootloader")?,
                record.as_deref(),
                sa.as_deref(),
                sb.as_deref(),
            )?)
        }
        "tuf-root" => a.write(&tuf::pinned_root(&a.read("root")?)?),
        "tuf-package" => {
            let roots = match a.opt("roots") {
                Some(list) => list
                    .split(',')
                    .map(|p| fs::read(p).map_err(|e| format!("{p}: {e}")))
                    .collect::<Result<Vec<_>, _>>()?,
                None => Vec::new(),
            };
            a.write(&tuf::package(
                &roots,
                &a.read("targets")?,
                &a.read("trusted-root")?,
            )?)
        }
        "tuf-verify" => {
            let v = tuf::verify(&a.read("pinned")?, &a.read("tuf")?)?;
            println!(
                "verified: root version {}, expires at {}",
                v.root_version, v.expires
            );
            Ok(())
        }
        "tuf-accept" => {
            let accepted = tuf::accept(
                &a.read("image")?,
                &a.read("bundle")?,
                &a.read("tuf")?,
                &a.read("pinned")?,
                &policy(a)?,
                level(a)?,
            )?;
            println!(
                "accepted: level {}, entry {:#x}, signed at {}",
                accepted.level, accepted.header.entry_point, accepted.signed_time
            );
            Ok(())
        }
        "tuf-dev-root" => {
            let keys = tuf::DevKeys::read(Path::new(a.get("keys")?))?;
            a.write(&keys.root(a.number("version")?)?)
        }
        "tuf-dev-targets" => {
            let keys = tuf::DevKeys::read(Path::new(a.get("keys")?))?;
            a.write(&keys.targets(
                a.number("root-version")?,
                &a.read("trusted-root")?,
                a.opt("expires").unwrap_or(tuf::DEV_EXPIRES),
            )?)
        }
        "help" | "-h" | "--help" => {
            println!("{USAGE}");
            Ok(())
        }
        other => Err(format!("unknown command {other}\n{USAGE}")),
    }
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    let Some(command) = argv.get(1) else {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    };
    let result = Args::parse(argv.get(2..).unwrap_or(&[])).and_then(|a| run(command, &a));
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("c3-ota: {e}");
            ExitCode::FAILURE
        }
    }
}

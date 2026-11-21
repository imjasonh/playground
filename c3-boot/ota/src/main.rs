//! `c3-ota`: build, sign, and check c3-boot slots.
//!
//! Run `c3-ota help` for the subcommands.

use std::collections::HashMap;
use std::fs;
use std::process::ExitCode;

use c3_ota::blob;
use c3_ota::container;
use c3_ota::image;
use c3_ota::keys;
use c3_ota::slot;
use c3_verify::bootstate;

const USAGE: &str = "usage: c3-ota <command> [--flag value]...

commands:
  pubkey --seed FILE                         print a seed's public key (hex)
  pack --elf FILE --security-version N --out FILE
  bootloader-image --elf FILE --out FILE
  container --bundle FILE [--image FILE] --out FILE
  link --level N --keys HEX,HEX --signers I=SEED,I=SEED --out FILE
  chain [--links FILE,FILE] --out FILE
  blob --trusted-root FILE --level N [--sequence N] --issuer S
       --build-signer-uri S --repository-id S --owner-id S --trigger S
       --signers I=SEED,I=SEED --out FILE
  describe --trusted-root FILE                print what a blob would trust
  slot --image FILE --bundle FILE --chain FILE --blob FILE --out FILE
  verify --slot FILE --genesis FILE [--level N]
  record --preferred a|b [--trial a|b --boots N] [--confirmed a,b]
         [--generation N] --out FILE
  flash --bootloader FILE [--record FILE] [--slot-a FILE] [--slot-b FILE] --out FILE";

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

fn signers(spec: &str) -> Result<Vec<(u8, ed25519_dalek::SigningKey)>, String> {
    spec.split(',')
        .map(|item| {
            let (index, path) = item.split_once('=').ok_or("signers look like I=SEEDFILE")?;
            let index: u8 = index.parse().map_err(|_| "signer index isn't a number")?;
            Ok((index, keys::read_signing_key(path)?))
        })
        .collect()
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
        "pubkey" => {
            let key = keys::read_signing_key(a.get("seed")?)?;
            let hex: String = key
                .verifying_key()
                .to_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("{hex}");
            Ok(())
        }
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
        "link" => {
            let keys: Vec<[u8; 32]> = a
                .get("keys")?
                .split(',')
                .map(|k| {
                    let mut out = [0u8; 32];
                    for (i, b) in out.iter_mut().enumerate() {
                        *b = u8::from_str_radix(k.get(2 * i..2 * i + 2).ok_or("short key")?, 16)
                            .map_err(|e| e.to_string())?;
                    }
                    Ok(out)
                })
                .collect::<Result<_, String>>()?;
            let s = signers(a.get("signers")?)?;
            let refs: Vec<_> = s.iter().map(|(i, k)| (*i, k)).collect();
            a.write(&blob::signed_link(a.number("level")?, &keys, &refs)?)
        }
        "chain" => {
            let links = match a.opt("links") {
                Some(list) => list
                    .split(',')
                    .map(|p| fs::read(p).map_err(|e| format!("{p}: {e}")))
                    .collect::<Result<Vec<_>, _>>()?,
                None => Vec::new(),
            };
            a.write(&blob::chain(&links)?)
        }
        "blob" => {
            let json = String::from_utf8(a.read("trusted-root")?).map_err(|e| e.to_string())?;
            let policy = [
                a.get("issuer")?.to_string(),
                a.get("build-signer-uri")?.to_string(),
                a.get("repository-id")?.to_string(),
                a.get("owner-id")?.to_string(),
                a.get("trigger")?.to_string(),
            ];
            let mut spec =
                blob::TrustRootSpec::from_trusted_root(&json, a.number("level")?, policy)?;
            if a.opt("sequence").is_some() {
                spec.sequence = a.number("sequence")?;
            }
            let s = signers(a.get("signers")?)?;
            let refs: Vec<_> = s.iter().map(|(i, k)| (*i, k)).collect();
            a.write(&blob::signed_blob(&spec, &refs)?)
        }
        "describe" => {
            let json = String::from_utf8(a.read("trusted-root")?).map_err(|e| e.to_string())?;
            let policy = Default::default();
            let spec = blob::TrustRootSpec::from_trusted_root(&json, 0, policy)?;
            print!("{}", spec.describe()?);
            Ok(())
        }
        "slot" => a.write(&slot::assemble(
            &a.read("image")?,
            &a.read("bundle")?,
            &a.read("chain")?,
            &a.read("blob")?,
        )?),
        "verify" => {
            let genesis: [u8; 128] = a
                .read("genesis")?
                .try_into()
                .map_err(|_| "genesis file isn't 128 bytes")?;
            let level = if a.opt("level").is_some() {
                a.number("level")?
            } else {
                0
            };
            let accepted = slot::verify(&a.read("slot")?, &genesis, level)?;
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

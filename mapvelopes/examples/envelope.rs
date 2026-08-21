//! Write an envelope PDF to disk so you can open it without deploying.
//!
//! ```bash
//! export GOOGLE_MAPS_API_KEY='…'
//! cargo run --example envelope
//! cargo run --example envelope -- --from 'Ada Example
//! 1600 Amphitheatre Parkway
//! Mountain View, CA 94043' --to 'Bob Example
//! 350 Fifth Avenue
//! New York, NY 10118' -o /tmp/envelope.pdf
//! ```
//!
//! If `GOOGLE_MAPS_API_KEY` is set (or `--key` is passed), the example geocodes
//! both addresses, fetches driving directions, and downloads a Static Maps JPEG.
//! Without a usable key the example exits with an error.

use std::env;
use std::io::Read;
use std::process::ExitCode;
use std::time::Duration;

use mapvelopes_worker::address::Address;
use mapvelopes_worker::error::Error;
use mapvelopes_worker::maps::{
    api_key_usable, directions_url, geocode_url, parse_directions, parse_geocode, spec_from_google,
    static_map_url, EnvelopeSize, EnvelopeSpec, MapStyle,
};
use mapvelopes_worker::render;

const DEFAULT_FROM: &str = "Ada Example\n1600 Amphitheatre Parkway\nMountain View, CA 94043";
const DEFAULT_TO: &str = "Bob Example\n350 Fifth Avenue\nNew York, NY 10118";

const USAGE: &str = "\
Write a US envelope PDF with the route from sender to recipient.

Usage:
  cargo run --example envelope -- [options]

Options:
  --from TEXT     Return address (default: a Mountain View example)
  --to TEXT       Delivery address (default: a New York example)
  -o, --out PATH  Output PDF (default: envelope.pdf)
  --style NAME    google, paper, terrain, muted, or hybrid (default: google)
  --size NAME     10, 9, monarch, 6-3/4, or a7 (default: 10)
  --key KEY       Google Maps API key (default: $GOOGLE_MAPS_API_KEY)
  -h, --help      Show this help
";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(1)
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return Ok(());
    }
    let parsed = parse_args(&args)?;
    let from = Address::parse_named("from", &parsed.from).map_err(|e| e.to_string())?;
    let to = Address::parse_named("to", &parsed.to).map_err(|e| e.to_string())?;

    if !api_key_usable(parsed.key.as_deref()) {
        return Err(Error::missing_maps_key().to_string());
    }
    let key = parsed.key.as_deref().expect("usable key");
    let spec = live_spec(from, to, parsed.style, parsed.size, key)?;

    let pdf = render(&spec).map_err(|e| e.to_string())?;
    std::fs::write(&parsed.out, &pdf).map_err(|e| format!("{}: {e}", parsed.out))?;
    eprintln!("wrote {} ({} bytes)", parsed.out, pdf.len());
    Ok(())
}

struct Args {
    from: String,
    to: String,
    out: String,
    key: Option<String>,
    style: MapStyle,
    size: EnvelopeSize,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut from = None;
    let mut to = None;
    let mut out = None;
    let mut key = env::var("GOOGLE_MAPS_API_KEY").ok();
    let mut style = MapStyle::Google;
    let mut size = EnvelopeSize::Ten;
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--from" => {
                from = Some(need_value(args, &mut i, "--from")?);
            }
            "--to" => {
                to = Some(need_value(args, &mut i, "--to")?);
            }
            "-o" | "--out" => {
                out = Some(need_value(args, &mut i, a)?);
            }
            "--key" => {
                key = Some(need_value(args, &mut i, "--key")?);
            }
            "--style" => {
                let raw = need_value(args, &mut i, "--style")?;
                style = MapStyle::parse(Some(&raw)).map_err(|e| e.to_string())?;
            }
            "--size" => {
                let raw = need_value(args, &mut i, "--size")?;
                size = EnvelopeSize::parse(Some(&raw)).map_err(|e| e.to_string())?;
            }
            other if other.starts_with("--from=") => {
                from = Some(other[7..].to_string());
                i += 1;
            }
            other if other.starts_with("--to=") => {
                to = Some(other[5..].to_string());
                i += 1;
            }
            other if other.starts_with("--out=") => {
                out = Some(other[6..].to_string());
                i += 1;
            }
            other if other.starts_with("--key=") => {
                key = Some(other[6..].to_string());
                i += 1;
            }
            other if other.starts_with("--style=") => {
                style = MapStyle::parse(Some(&other[8..])).map_err(|e| e.to_string())?;
                i += 1;
            }
            other if other.starts_with("--size=") => {
                size = EnvelopeSize::parse(Some(&other[7..])).map_err(|e| e.to_string())?;
                i += 1;
            }
            other => return Err(format!("unknown argument: {other}\n{USAGE}")),
        }
    }
    Ok(Args {
        from: from.unwrap_or_else(|| DEFAULT_FROM.to_string()),
        to: to.unwrap_or_else(|| DEFAULT_TO.to_string()),
        out: out.unwrap_or_else(|| "envelope.pdf".to_string()),
        key,
        style,
        size,
    })
}

fn need_value(args: &[String], i: &mut usize, flag: &str) -> Result<String, String> {
    let next = args
        .get(*i + 1)
        .ok_or_else(|| format!("{flag} needs a value"))?;
    *i += 2;
    Ok(next.clone())
}

fn live_spec(
    from: Address,
    to: Address,
    style: MapStyle,
    size: EnvelopeSize,
    key: &str,
) -> Result<EnvelopeSpec, String> {
    let agent = ureq::AgentBuilder::new()
        .timeout(Duration::from_secs(25))
        .user_agent("mapvelopes/0.1")
        .build();
    let from_body = http_get(&agent, &geocode_url(&from.geocode_query(), key))?;
    let to_body = http_get(&agent, &geocode_url(&to.geocode_query(), key))?;
    let from_ll = parse_geocode(&from_body).map_err(|e| e.to_string())?;
    let to_ll = parse_geocode(&to_body).map_err(|e| e.to_string())?;
    let dir_body = http_get(
        &agent,
        &directions_url(from_ll.location, to_ll.location, key),
    )?;
    let route = parse_directions(&dir_body).map_err(|e| e.to_string())?;
    let jpeg = http_get(&agent, &static_map_url(&route, key, style, size))?;
    spec_from_google(
        from, to, &from_body, &to_body, &dir_body, &jpeg, style, size,
    )
    .map_err(|e| e.to_string())
}

fn http_get(agent: &ureq::Agent, url: &str) -> Result<Vec<u8>, String> {
    let resp = agent.get(url).call().map_err(|e| e.to_string())?;
    let mut buf = Vec::new();
    resp.into_reader()
        .read_to_end(&mut buf)
        .map_err(|e| e.to_string())?;
    Ok(buf)
}

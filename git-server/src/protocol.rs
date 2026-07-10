//! The git smart-HTTP wire protocol.
//!
//! * **Fetch**: protocol v2 (gitprotocol-v2(5)) — `ls-refs` and `fetch`
//!   commands over stateless HTTP POSTs. v2 is what every git ≥ 2.26 speaks
//!   by default, and its stateless-first design maps perfectly onto Workers
//!   (no connection state between rounds). Negotiation is short-circuited:
//!   we ACK every common `have` and declare `ready`, sending the pack in the
//!   same response — one round trip for fetches, which also minimizes billable
//!   requests.
//! * **Push**: the classic receive-pack flow (gitprotocol-pack(5)) — the ref
//!   advertisement, then a POST whose body is ref-update commands followed by
//!   a pack, answered with report-status. (There is no protocol v2 for push.)
//!
//! Handlers are transport-agnostic: they take a [`BodyStream`] (so a push
//! pack is streamed to R2 as it arrives, never buffered) and return response
//! bytes.

use crate::object::Oid;
use crate::pktline::{self, band, Pkt, PktParser};
use crate::refs::RepoState;
use crate::repo::{collect_fetch_set, PackIngest, RefUpdate, Repo};
use std::collections::BTreeMap;

/// Server agent string advertised to clients.
pub const AGENT: &str = "git-server-worker/0.1";

/// Incremental request-body source. Implemented over the Workers request
/// stream and over the native test server's reader.
#[async_trait::async_trait(?Send)]
pub trait BodyStream {
    /// Next chunk, `None` at end of body.
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String>;
}

/// A fully buffered body (fine for the small upload-pack negotiation bodies).
pub struct BufferedBody(Option<Vec<u8>>);

impl BufferedBody {
    pub fn new(bytes: Vec<u8>) -> Self {
        BufferedBody(Some(bytes))
    }
}

#[async_trait::async_trait(?Send)]
impl BodyStream for BufferedBody {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        Ok(self.0.take())
    }
}

// ---------------------------------------------------------------------------
// info/refs advertisements
// ---------------------------------------------------------------------------

/// `GET /<repo>/info/refs?service=git-upload-pack` with `Git-Protocol:
/// version=2` — the v2 capability advertisement.
pub fn advertise_upload_pack_v2() -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&pktline::text_pkt("# service=git-upload-pack"));
    out.extend_from_slice(pktline::flush_pkt());
    out.extend_from_slice(&pktline::text_pkt("version 2"));
    out.extend_from_slice(&pktline::text_pkt(&format!("agent={AGENT}")));
    out.extend_from_slice(&pktline::text_pkt("ls-refs=unborn"));
    out.extend_from_slice(&pktline::text_pkt("fetch=thin-pack"));
    out.extend_from_slice(&pktline::text_pkt("object-format=sha1"));
    out.extend_from_slice(pktline::flush_pkt());
    out
}

/// `GET /<repo>/info/refs?service=git-receive-pack` — the classic (v0) ref
/// advertisement that push uses.
pub fn advertise_receive_pack(state: &RepoState) -> Vec<u8> {
    let caps =
        format!("report-status delete-refs side-band-64k quiet object-format=sha1 agent={AGENT}");
    let mut out = Vec::new();
    out.extend_from_slice(&pktline::text_pkt("# service=git-receive-pack"));
    out.extend_from_slice(pktline::flush_pkt());
    let refs: Vec<(&String, &String)> = state.refs.iter().collect();
    if refs.is_empty() {
        out.extend_from_slice(&pktline::text_pkt(&format!(
            "{} capabilities^{{}}\0{caps}",
            "0".repeat(40)
        )));
    } else {
        for (i, (name, oid)) in refs.iter().enumerate() {
            if i == 0 {
                out.extend_from_slice(&pktline::text_pkt(&format!("{oid} {name}\0{caps}")));
            } else {
                out.extend_from_slice(&pktline::text_pkt(&format!("{oid} {name}")));
            }
        }
    }
    out.extend_from_slice(pktline::flush_pkt());
    out
}

// ---------------------------------------------------------------------------
// upload-pack (protocol v2)
// ---------------------------------------------------------------------------

/// Handle a `POST /<repo>/git-upload-pack` body (protocol v2 command
/// request). Negotiation bodies are small, so buffering them is fine.
pub async fn upload_pack(repo: &Repo<'_>, body: &[u8]) -> Result<Vec<u8>, String> {
    let pkts = pktline::parse_all(body).map_err(|e| e.to_string())?;
    let mut it = pkts.iter();
    let command = loop {
        match it.next() {
            Some(pkt) => {
                if let Some(text) = pkt.as_text() {
                    if let Some(c) = text.strip_prefix("command=") {
                        break c.to_string();
                    }
                    // capability lines (agent=, object-format=) — accept.
                }
            }
            None => return Err("missing command".into()),
        }
    };
    // Collect argument lines (after the delim, until flush).
    let mut args: Vec<String> = Vec::new();
    let mut in_args = false;
    for pkt in it {
        match pkt {
            Pkt::Delim => in_args = true,
            Pkt::Flush => break,
            Pkt::Data(_) if in_args => {
                if let Some(t) = pkt.as_text() {
                    args.push(t.to_string());
                }
            }
            Pkt::Data(_) => {
                if let Some(t) = pkt.as_text() {
                    // Tolerate capability lines before the delim.
                    let _ = t;
                }
            }
            _ => {}
        }
    }

    match command.as_str() {
        "ls-refs" => ls_refs(repo, &args).await,
        "fetch" => fetch(repo, &args).await,
        other => Ok(error_response(&format!("unknown command {other}"))),
    }
}

async fn ls_refs(repo: &Repo<'_>, args: &[String]) -> Result<Vec<u8>, String> {
    let (state, _) = repo.load_state().await?;
    let mut symrefs = false;
    let mut unborn = false;
    let mut peel = false;
    let mut prefixes: Vec<String> = Vec::new();
    for a in args {
        match a.as_str() {
            "symrefs" => symrefs = true,
            "unborn" => unborn = true,
            "peel" => peel = true,
            _ => {
                if let Some(p) = a.strip_prefix("ref-prefix ") {
                    prefixes.push(p.to_string());
                }
            }
        }
    }
    let matches =
        |name: &str| prefixes.is_empty() || prefixes.iter().any(|p| name.starts_with(p.as_str()));

    let mut out = Vec::new();
    // HEAD first (git expects it for clone default-branch selection).
    if matches("HEAD") {
        match state.head_oid() {
            Some(oid) => {
                let mut line = format!("{oid} HEAD");
                if symrefs {
                    line.push_str(&format!(" symref-target:{}", state.head));
                }
                out.extend_from_slice(&pktline::text_pkt(&line));
            }
            None if unborn => {
                let mut line = "unborn HEAD".to_string();
                if symrefs {
                    line.push_str(&format!(" symref-target:{}", state.head));
                }
                out.extend_from_slice(&pktline::text_pkt(&line));
            }
            None => {}
        }
    }
    // Annotated-tag peeling needs the odb; open it lazily only if asked.
    let odb = if peel && !state.packs.is_empty() {
        Some(repo.odb(&state).await?)
    } else {
        None
    };
    for (name, oid_hex) in &state.refs {
        if !matches(name) {
            continue;
        }
        let mut line = format!("{oid_hex} {name}");
        if let (Some(odb), Some(oid)) = (&odb, Oid::from_hex(oid_hex)) {
            if let Ok(Some((crate::object::ObjType::Tag, _))) = odb.read(oid).await {
                if let Ok(peeled) = odb.peel_to_commit(oid).await {
                    line.push_str(&format!(" peeled:{peeled}"));
                }
            }
        }
        out.extend_from_slice(&pktline::text_pkt(&line));
    }
    out.extend_from_slice(pktline::flush_pkt());
    Ok(out)
}

async fn fetch(repo: &Repo<'_>, args: &[String]) -> Result<Vec<u8>, String> {
    let mut wants: Vec<Oid> = Vec::new();
    let mut haves: Vec<Oid> = Vec::new();
    let mut done = false;
    let mut thin_pack = false;
    let mut no_progress = false;
    for a in args {
        if let Some(w) = a.strip_prefix("want ") {
            wants.push(Oid::from_hex(w).ok_or("bad want oid")?);
        } else if let Some(h) = a.strip_prefix("have ") {
            haves.push(Oid::from_hex(h).ok_or("bad have oid")?);
        } else {
            match a.as_str() {
                "done" => done = true,
                "thin-pack" => thin_pack = true,
                "no-progress" => no_progress = true,
                "ofs-delta" | "include-tag" | "wait-for-done" => {}
                other
                    if other.starts_with("shallow")
                        || other.starts_with("deepen")
                        || other.starts_with("filter") =>
                {
                    return Ok(error_response(&format!(
                        "unsupported fetch option: {other}"
                    )));
                }
                _ => {}
            }
        }
    }
    if wants.is_empty() {
        return Ok(error_response("fetch: no wants"));
    }

    let (state, _) = repo.load_state().await?;
    if state.packs.is_empty() {
        return Ok(error_response("repository is empty"));
    }
    let odb = repo.odb(&state).await?;
    let set = collect_fetch_set(&odb, &wants, &haves).await?;

    let mut out = Vec::new();
    if !done {
        // Stateless negotiation: acknowledge commons and declare ready — the
        // pack follows in this same response, so fetch is one round trip.
        out.extend_from_slice(&pktline::text_pkt("acknowledgments"));
        if set.common.is_empty() {
            out.extend_from_slice(&pktline::text_pkt("NAK"));
        } else {
            for c in &set.common {
                out.extend_from_slice(&pktline::text_pkt(&format!("ACK {c}")));
            }
        }
        out.extend_from_slice(&pktline::text_pkt("ready"));
        out.extend_from_slice(pktline::delim_pkt());
    }
    out.extend_from_slice(&pktline::text_pkt("packfile"));
    if !no_progress {
        let mut msg = Vec::new();
        msg.push(band::PROGRESS);
        msg.extend_from_slice(format!("packing {} objects\r\n", set.include.len()).as_bytes());
        out.extend_from_slice(&pktline::data_pkt(&msg));
    }
    let pack = crate::repo::build_pack(&odb, &set, thin_pack).await?;
    pktline::write_band_pkts(&mut out, band::DATA, &pack);
    out.extend_from_slice(pktline::flush_pkt());
    Ok(out)
}

/// A v2 error response (`ERR` pkt).
fn error_response(message: &str) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&pktline::text_pkt(&format!("ERR {message}")));
    out.extend_from_slice(pktline::flush_pkt());
    out
}

// ---------------------------------------------------------------------------
// receive-pack (push)
// ---------------------------------------------------------------------------

/// Handle a `POST /<repo>/git-receive-pack` body: pkt-line ref-update
/// commands, a flush, then (unless every command is a delete) the pack —
/// which is streamed straight into R2 while being scanned.
///
/// `nonce` provides per-push uniqueness for the staged pack's storage key
/// (randomness is the caller's responsibility; this crate is runtime-
/// agnostic).
pub async fn receive_pack(
    repo: &Repo<'_>,
    body: &mut dyn BodyStream,
    nonce: &str,
) -> Result<Vec<u8>, String> {
    let (state, version) = repo.load_state().await?;

    // Phase 1: pkt-line command section.
    let mut parser = PktParser::new();
    let mut commands: Vec<RefUpdate> = Vec::new();
    let mut caps: BTreeMap<String, String> = BTreeMap::new();
    let mut saw_flush = false;
    while !saw_flush {
        let chunk = match body.next_chunk().await? {
            Some(c) => c,
            None => break,
        };
        parser.feed(&chunk);
        while let Some(pkt) = parser.next_pkt().map_err(|e| e.to_string())? {
            match pkt {
                Pkt::Flush => {
                    saw_flush = true;
                    break;
                }
                Pkt::Data(_) => {
                    let text = pkt.as_text().ok_or("non-text command pkt")?;
                    let (cmd_part, caps_part) = match text.split_once('\0') {
                        Some((c, k)) => (c, Some(k)),
                        None => (text, None),
                    };
                    if let Some(k) = caps_part {
                        for cap in k.split(' ').filter(|s| !s.is_empty()) {
                            match cap.split_once('=') {
                                Some((name, value)) => {
                                    caps.insert(name.to_string(), value.to_string())
                                }
                                None => caps.insert(cap.to_string(), String::new()),
                            };
                        }
                    }
                    let mut fields = cmd_part.split(' ');
                    let old = fields
                        .next()
                        .and_then(Oid::from_hex)
                        .ok_or("bad old oid in command")?;
                    let new = fields
                        .next()
                        .and_then(Oid::from_hex)
                        .ok_or("bad new oid in command")?;
                    let name = fields.next().ok_or("missing ref name")?.to_string();
                    if !valid_ref_name(&name) {
                        return Err(format!("invalid ref name {name}"));
                    }
                    commands.push(RefUpdate { name, old, new });
                }
                _ => return Err("unexpected pkt in command section".into()),
            }
        }
    }
    if commands.is_empty() {
        // "Everything up to date" push: reply with an empty report.
        return Ok(report_status(&caps, "unpack ok", &[]));
    }

    // Phase 2: the pack, streamed to R2 while scanned. Deletes-only pushes
    // carry no pack.
    let expect_pack = commands.iter().any(|c| !c.new.is_zero());
    let ingested = if expect_pack {
        let mut ingest = PackIngest::start(repo, nonce).await?;
        let mut got_any = false;
        let leftover = parser.take_remainder();
        if !leftover.is_empty() {
            got_any = true;
            if let Err(e) = ingest.feed(&leftover).await {
                let _ = ingest.abort().await;
                return Err(e);
            }
        }
        loop {
            match body.next_chunk().await? {
                Some(chunk) if !chunk.is_empty() => {
                    got_any = true;
                    if let Err(e) = ingest.feed(&chunk).await {
                        let _ = ingest.abort().await;
                        return Err(e);
                    }
                }
                Some(_) => {}
                None => break,
            }
        }
        if !got_any {
            let _ = ingest.abort().await;
            return Err("push updates refs but sent no pack".into());
        }
        match ingest.finish().await {
            Ok(v) => Some(v),
            Err(e) => {
                return Ok(report_status(
                    &caps,
                    &format!("unpack {e}"),
                    &commands
                        .iter()
                        .map(|c| (c.name.clone(), Some("unpacker error".to_string())))
                        .collect::<Vec<_>>(),
                ))
            }
        }
    } else {
        None
    };

    // Phase 3: resolve, index, build derived indexes, CAS the state.
    let outcome = repo.apply_push(commands, ingested, state, version).await?;
    let lines: Vec<(String, Option<String>)> = outcome
        .results
        .iter()
        .map(|r| (r.name.clone(), r.error.clone()))
        .collect();
    Ok(report_status(&caps, "unpack ok", &lines))
}

/// Format a report-status response, side-band-wrapped if negotiated.
fn report_status(
    caps: &BTreeMap<String, String>,
    unpack: &str,
    refs: &[(String, Option<String>)],
) -> Vec<u8> {
    let mut report = Vec::new();
    report.extend_from_slice(&pktline::text_pkt(unpack));
    for (name, err) in refs {
        match err {
            None => report.extend_from_slice(&pktline::text_pkt(&format!("ok {name}"))),
            Some(reason) => {
                report.extend_from_slice(&pktline::text_pkt(&format!("ng {name} {reason}")))
            }
        }
    }
    report.extend_from_slice(pktline::flush_pkt());

    if caps.contains_key("side-band-64k") {
        let mut out = Vec::new();
        pktline::write_band_pkts(&mut out, band::DATA, &report);
        out.extend_from_slice(pktline::flush_pkt());
        out
    } else {
        report
    }
}

/// Ref-name hygiene (subset of git-check-ref-format rules; enough to keep
/// storage keys and state clean).
fn valid_ref_name(name: &str) -> bool {
    if !name.starts_with("refs/") || name.ends_with('/') || name.ends_with('.') {
        return false;
    }
    if name.contains("..") || name.contains("//") || name.contains("@{") {
        return false;
    }
    name.bytes().all(|b| {
        !b.is_ascii_control()
            && !matches!(b, b' ' | b'~' | b'^' | b':' | b'?' | b'*' | b'[' | b'\\')
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ref_name_validation() {
        assert!(valid_ref_name("refs/heads/main"));
        assert!(valid_ref_name("refs/tags/v1.0.0"));
        assert!(!valid_ref_name("main"));
        assert!(!valid_ref_name("refs/heads/a..b"));
        assert!(!valid_ref_name("refs/heads/sp ace"));
        assert!(!valid_ref_name("refs/heads/x/"));
        assert!(!valid_ref_name("refs/heads/x."));
        assert!(!valid_ref_name("refs/heads/@{now}"));
    }

    #[test]
    fn receive_pack_advertisement_empty_repo() {
        let state = RepoState::empty();
        let ad = advertise_receive_pack(&state);
        let text = String::from_utf8_lossy(&ad);
        assert!(text.contains("# service=git-receive-pack"));
        assert!(text.contains("capabilities^{}"));
        assert!(text.contains("report-status"));
    }

    #[test]
    fn upload_pack_advertisement_shape() {
        let ad = advertise_upload_pack_v2();
        let pkts = pktline::parse_all(&ad).unwrap();
        let texts: Vec<String> = pkts
            .iter()
            .filter_map(|p| p.as_text().map(String::from))
            .collect();
        assert!(texts.contains(&"version 2".to_string()));
        assert!(texts.iter().any(|t| t.starts_with("ls-refs")));
        assert!(texts.iter().any(|t| t.starts_with("fetch")));
    }
}

//! Isolate memory-budget enforcement.
//!
//! Production runs under a hard 128 MiB Workers isolate limit; exceeding it
//! is Cloudflare error 1102 (the client sees a 503) — and, because wasm
//! linear memory never shrinks, one bloated request degrades the isolate for
//! all subsequent ones. These tests measure *peak live heap* while serving
//! large pushes and clones through the same handler the Worker runs, and
//! fail if a request's transient memory footprint could not fit the isolate.
//! This is the CI tripwire for exactly the class of buffering bug that
//! otherwise only shows up as production 503s.
//!
//! Methodology: a tracking global allocator records peak live bytes. The
//! repo payload is incompressible (worst case: pack bytes ≈ content bytes),
//! large enough (~48 MiB) that any accidental whole-body buffering or
//! double-copy shows up as a multiple of it. Because the in-memory Store
//! also lives on the test heap, assertions are on *peak minus baseline*,
//! with the legitimately-stored bytes accounted for explicitly.

use futures::executor::block_on;
use futures::StreamExt;
use git_server::http::{Body, GitHttp, Request as GitRequest};
use git_server::memtrack;
use git_server::object::{hash_object, ObjType, Oid};
use git_server::pack::write::PackWriter;
use git_server::pktline;
use git_server::protocol::BodyStream;
use git_server::refs::MemStateStore;
use git_server::storage::{MemStore, Store};

#[global_allocator]
static ALLOC: memtrack::TrackingAllocator = memtrack::TrackingAllocator::new();

/// Transient budget for one request: how much heap the handler may use *on
/// top of* bytes it legitimately persists to storage. Well under the 128 MiB
/// isolate limit, leaving room for the wasm module, the runtime, and the JS
/// side of the streamed body.
const TRANSIENT_BUDGET: usize = 64 * 1024 * 1024;

/// Bulk payload size. Big enough that a single accidental extra copy
/// (+48 MiB) blows TRANSIENT_BUDGET immediately.
const BULK_BYTES: usize = 48 * 1024 * 1024;

use git_server::testutil::deterministic_noise;

/// Build (commit oid, pack bytes) for a one-commit repo whose tree holds
/// `blobs` incompressible blobs of `blob_len` bytes each.
fn build_synthetic_pack(blobs: usize, blob_len: usize) -> (Oid, Vec<u8>) {
    let mut entries = Vec::new();
    let mut w = PackWriter::new((blobs + 2) as u32);
    let mut blob_oids = Vec::new();
    for i in 0..blobs {
        let data = deterministic_noise(blob_len, 0x9e3779b97f4a7c15 ^ i as u64);
        let oid = hash_object(ObjType::Blob, &data);
        w.add_full(ObjType::Blob, &data);
        blob_oids.push(oid);
    }
    for (i, oid) in blob_oids.iter().enumerate() {
        entries.push(git_server::object::TreeEntry {
            mode: "100644".into(),
            name: format!("blob{i:03}.bin"),
            oid: *oid,
        });
    }
    entries.sort_by(|a, b| a.name.cmp(&b.name));
    let tree = git_server::object::encode_tree(&entries);
    let tree_oid = hash_object(ObjType::Tree, &tree);
    w.add_full(ObjType::Tree, &tree);
    let commit = format!(
        "tree {tree_oid}\nauthor T <t@x> 1700000000 +0000\ncommitter T <t@x> 1700000000 +0000\n\nbig\n"
    );
    let commit_oid = hash_object(ObjType::Commit, commit.as_bytes());
    w.add_full(ObjType::Commit, commit.as_bytes());
    let (pack, _) = w.finish();
    (commit_oid, pack)
}

/// Serves a pre-built body in 64 KiB chunks, like a network transport, and
/// frees each chunk's source as it goes (so the request body itself doesn't
/// sit on the heap inflating the measurement — matching production, where
/// the body arrives from the network).
struct ChunkedBody {
    chunks: std::collections::VecDeque<Vec<u8>>,
}

impl ChunkedBody {
    fn new(bytes: Vec<u8>) -> ChunkedBody {
        let mut chunks = std::collections::VecDeque::new();
        for c in bytes.chunks(64 * 1024) {
            chunks.push_back(c.to_vec());
        }
        ChunkedBody { chunks }
    }
}

#[async_trait::async_trait(?Send)]
impl BodyStream for ChunkedBody {
    async fn next_chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        Ok(self.chunks.pop_front())
    }
}

fn mib(n: usize) -> f64 {
    n as f64 / (1024.0 * 1024.0)
}

#[test]
fn large_push_and_clone_fit_isolate_memory() {
    let store = MemStore::new();
    let states = MemStateStore::new();

    // --- Build the push request body (pre-request; not part of the budget).
    let (commit_oid, pack) = build_synthetic_pack(12, BULK_BYTES / 12);
    let pack_len = pack.len();
    let mut push_body = Vec::new();
    push_body.extend_from_slice(&pktline::text_pkt(&format!(
        "{} {} refs/heads/main\0report-status side-band-64k agent=test",
        "0".repeat(40),
        commit_oid
    )));
    push_body.extend_from_slice(pktline::flush_pkt());
    push_body.extend_from_slice(&pack);
    drop(pack);
    let mut body = ChunkedBody::new(push_body);

    // --- Push, measuring peak heap during the request. -----------------------
    let stored_before: u64 = stored_bytes(&store);
    let live_before = memtrack::live_bytes();
    memtrack::reset_peak();
    let resp = block_on(async {
        let server = GitHttp::new(
            std::rc::Rc::new(store.clone()),
            std::rc::Rc::new(states.clone()),
        );
        let req = GitRequest {
            method: "POST",
            path: "/big/git-receive-pack",
            query: None,
            git_protocol: None,
            content_encoding: None,
            cf_ray: None,
        };
        server.handle(&req, &mut body, "mem-push").await
    });
    assert_eq!(resp.status, 200);
    let report = String::from_utf8_lossy(match &resp.body {
        Body::Full(b) => b,
        Body::Stream(_) => panic!("push responses are not streamed"),
    })
    .to_string();
    assert!(report.contains("unpack ok"), "{report}");
    drop(resp);

    let push_peak_delta = memtrack::peak_delta_since_reset(live_before);
    let stored_growth = (stored_bytes(&store) - stored_before) as usize;
    let push_transient = push_peak_delta.saturating_sub(stored_growth);
    println!(
        "push:  pack {:.1} MiB; peak-delta {:.1} MiB; stored-growth {:.1} MiB; transient {:.1} MiB",
        mib(pack_len),
        mib(push_peak_delta),
        mib(stored_growth),
        mib(push_transient)
    );
    assert!(
        push_transient < TRANSIENT_BUDGET,
        "push used {:.1} MiB transient heap (budget {:.1} MiB): a {:.1} MiB push \
         would exceed the Workers isolate limit in production (error 1102 / 503)",
        mib(push_transient),
        mib(TRANSIENT_BUDGET),
        mib(pack_len),
    );

    // --- Clone (protocol v2 fetch with done), measuring peak heap. -----------
    let mut fetch_body = Vec::new();
    fetch_body.extend_from_slice(&pktline::text_pkt("command=fetch"));
    fetch_body.extend_from_slice(&pktline::text_pkt("object-format=sha1"));
    fetch_body.extend_from_slice(pktline::delim_pkt());
    fetch_body.extend_from_slice(&pktline::text_pkt("no-progress"));
    fetch_body.extend_from_slice(&pktline::text_pkt(&format!("want {commit_oid}")));
    fetch_body.extend_from_slice(&pktline::text_pkt("done"));
    fetch_body.extend_from_slice(pktline::flush_pkt());
    let mut body = ChunkedBody::new(fetch_body);

    let live_before = memtrack::live_bytes();
    memtrack::reset_peak();
    let total_streamed = block_on(async {
        let server = GitHttp::new(
            std::rc::Rc::new(store.clone()),
            std::rc::Rc::new(states.clone()),
        );
        let req = GitRequest {
            method: "POST",
            path: "/big/git-upload-pack",
            query: None,
            git_protocol: Some("version=2"),
            content_encoding: None,
            cf_ray: None,
        };
        let resp = server.handle(&req, &mut body, "mem-clone").await;
        assert_eq!(resp.status, 200);
        // Drain the response the way the Workers runtime would: chunk by
        // chunk, each dropped after relay.
        match resp.body {
            Body::Full(b) => b.len() as u64,
            Body::Stream(mut s) => {
                let mut total = 0u64;
                while let Some(chunk) = s.next().await {
                    total += chunk.expect("stream chunk").len() as u64;
                }
                total
            }
        }
    });
    let clone_peak_delta = memtrack::peak_delta_since_reset(live_before);
    println!(
        "clone: streamed {:.1} MiB; peak-delta {:.1} MiB",
        total_streamed as f64 / (1024.0 * 1024.0),
        mib(clone_peak_delta)
    );
    assert!(
        total_streamed as usize > BULK_BYTES,
        "clone response should carry the whole repo"
    );
    assert!(
        clone_peak_delta < TRANSIENT_BUDGET,
        "clone used {:.1} MiB transient heap (budget {:.1} MiB): cloning a \
         {:.1} MiB repo would exceed the Workers isolate limit in production \
         (error 1102 / 503)",
        mib(clone_peak_delta),
        mib(TRANSIENT_BUDGET),
        mib(pack_len),
    );
}

fn stored_bytes(store: &MemStore) -> u64 {
    store
        .keys()
        .iter()
        .map(|k| block_on(store.size(k)).unwrap().unwrap_or(0))
        .sum()
}

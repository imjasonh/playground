//! Request-scoped metrics: phase timings and backend operation counts.
//!
//! The point is to make production behave like the benchmarks: every response
//! carries the same numbers the cost model is built on (R2 Class A/B ops, DO
//! requests, KV ops, per-phase milliseconds), so deployed assumptions can be
//! checked with `scripts/bench-remote.sh` or plain `curl -v` instead of
//! guesswork.
//!
//! Collection is a thread-local since both runtimes handle one request per
//! thread at a time (wasm isolates are single-threaded; the native test
//! server drives each request with a local executor). [`begin`] resets the
//! collector, instrumented code records into it ([`backend`], [`phase`],
//! bytes), and [`take`] returns the totals for emission as:
//!
//! * a `Server-Timing` response header (standard, machine-parseable, visible
//!   to `curl` and browser dev tools) — see [`Metrics::server_timing`];
//! * a structured JSON log line (Workers Logs / `wrangler tail`) — see
//!   [`Metrics::log_json`] — which covers the git-protocol endpoints whose
//!   response headers a git client never shows you.
//!
//! Overhead is a few clock reads and integer adds per backend call; there is
//! no allocation until emission.

use std::cell::RefCell;

/// Backend operation kinds, mirroring what each costs money as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    /// R2 Class A (writes: put, multipart create/part/complete, delete).
    R2ClassA,
    /// R2 Class B (reads: get, ranged get, head).
    R2ClassB,
    /// Durable Object request (state load / commit).
    DoRequest,
    /// Workers KV read or write.
    Kv,
}

/// Totals for one request.
#[derive(Debug, Clone, Default)]
pub struct Metrics {
    pub r2_class_a: u64,
    pub r2_class_b: u64,
    pub do_requests: u64,
    pub kv_ops: u64,
    /// Total milliseconds awaited on backend calls (R2 + DO + KV). The gap
    /// between this and total request time is our own CPU.
    pub backend_ms: f64,
    /// Named pipeline phases (label, milliseconds), in completion order.
    pub phases: Vec<(&'static str, f64)>,
    pub bytes_in: u64,
    pub bytes_out: u64,
    /// Largest single request-body chunk observed. Diagnostic for edge
    /// buffering: if a chunked (Transfer-Encoding) upload arrives as one
    /// giant chunk instead of a stream of small ones, its JS+wasm copies
    /// blow the isolate memory limit — this field proves or disproves that
    /// from a single log line.
    pub max_chunk_in: u64,
}

thread_local! {
    static ACTIVE: RefCell<Option<Metrics>> = const { RefCell::new(None) };
}

/// Milliseconds on a monotonic-enough clock for both targets.
pub fn now_ms() -> f64 {
    #[cfg(target_arch = "wasm32")]
    {
        js_sys::Date::now()
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        use std::sync::OnceLock;
        use std::time::Instant;
        static START: OnceLock<Instant> = OnceLock::new();
        START.get_or_init(Instant::now).elapsed().as_secs_f64() * 1e3
    }
}

/// Start collecting for the current request (resets any previous state).
pub fn begin() {
    ACTIVE.with(|a| *a.borrow_mut() = Some(Metrics::default()));
}

/// Stop collecting and return the totals (None if `begin` was never called).
pub fn take() -> Option<Metrics> {
    ACTIVE.with(|a| a.borrow_mut().take())
}

fn with_active(f: impl FnOnce(&mut Metrics)) {
    ACTIVE.with(|a| {
        if let Some(m) = a.borrow_mut().as_mut() {
            f(m);
        }
    });
}

/// Record one backend operation and the milliseconds spent awaiting it.
pub fn backend(op: Op, ms: f64) {
    with_active(|m| {
        match op {
            Op::R2ClassA => m.r2_class_a += 1,
            Op::R2ClassB => m.r2_class_b += 1,
            Op::DoRequest => m.do_requests += 1,
            Op::Kv => m.kv_ops += 1,
        }
        m.backend_ms += ms;
    });
}

/// Record a completed pipeline phase.
pub fn phase(label: &'static str, ms: f64) {
    with_active(|m| m.phases.push((label, ms)));
}

pub fn add_bytes_in(n: u64) {
    with_active(|m| {
        m.bytes_in += n;
        if n > m.max_chunk_in {
            m.max_chunk_in = n;
        }
    });
}

pub fn add_bytes_out(n: u64) {
    with_active(|m| m.bytes_out += n);
}

/// Cloudflare list prices (2025-2026), $ per operation — the marginal
/// per-request cost model shared by production metrics, `docs/design.md`,
/// and the benchmarks. Storage and Worker invocation/CPU are excluded
/// (covered separately in `docs/design.md`).
pub mod cost {
    pub const R2_CLASS_A_USD: f64 = 4.50 / 1e6;
    pub const R2_CLASS_B_USD: f64 = 0.36 / 1e6;
    pub const DO_REQUEST_USD: f64 = 0.15 / 1e6;
    /// KV reads/writes differ ($0.50 vs $5.00 per M); the hot path only
    /// reads, so reads are what the model counts.
    pub const KV_READ_USD: f64 = 0.50 / 1e6;

    /// Marginal cost of a request that performed the given operation counts.
    pub fn marginal_usd(r2_class_a: u64, r2_class_b: u64, do_requests: u64, kv_reads: u64) -> f64 {
        r2_class_a as f64 * R2_CLASS_A_USD
            + r2_class_b as f64 * R2_CLASS_B_USD
            + do_requests as f64 * DO_REQUEST_USD
            + kv_reads as f64 * KV_READ_USD
    }
}

impl Metrics {
    /// Marginal request cost in USD (see [`cost`]).
    pub fn cost_usd(&self) -> f64 {
        cost::marginal_usd(
            self.r2_class_a,
            self.r2_class_b,
            self.do_requests,
            self.kv_ops,
        )
    }

    /// `Server-Timing` header value (RFC-style `name;dur=..;desc=".."`).
    ///
    /// `dur` carries milliseconds where that's meaningful; op counters ride
    /// in `desc` (Server-Timing has no count field). Example:
    /// `total;dur=12.3, backend;dur=8.0, r2a;desc="0", r2b;desc="7", ...`
    pub fn server_timing(&self, total_ms: f64) -> String {
        let mut parts = vec![
            format!("total;dur={total_ms:.1}"),
            format!("backend;dur={:.1}", self.backend_ms),
            format!("r2a;desc=\"{}\"", self.r2_class_a),
            format!("r2b;desc=\"{}\"", self.r2_class_b),
            format!("do;desc=\"{}\"", self.do_requests),
            format!("kv;desc=\"{}\"", self.kv_ops),
            format!("cost;desc=\"{:.3}u$\"", self.cost_usd() * 1e6),
            format!("maxchunk;desc=\"{}\"", self.max_chunk_in),
        ];
        for (label, ms) in &self.phases {
            // Phase labels become header-safe tokens: "push: stream+scan" →
            // "push_stream_scan".
            let token: String = label
                .chars()
                .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                .collect::<String>()
                .split('_')
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>()
                .join("_");
            parts.push(format!("{token};dur={ms:.1}"));
        }
        parts.join(", ")
    }

    /// One-line JSON for structured logs (Workers Logs / `wrangler tail`).
    pub fn log_json(&self, method: &str, path: &str, status: u16, total_ms: f64) -> String {
        let phases: Vec<String> = self
            .phases
            .iter()
            .map(|(l, ms)| format!("\"{l}\":{ms:.1}"))
            .collect();
        format!(
            "{{\"evt\":\"req\",\"method\":\"{method}\",\"path\":\"{path}\",\"status\":{status},\
             \"ms\":{total_ms:.1},\"backend_ms\":{:.1},\"r2a\":{},\"r2b\":{},\"do\":{},\"kv\":{},\
             \"bytes_in\":{},\"max_chunk_in\":{},\"bytes_out\":{},\"cost_usd\":{:.9},\"phases\":{{{}}}}}",
            self.backend_ms,
            self.r2_class_a,
            self.r2_class_b,
            self.do_requests,
            self.kv_ops,
            self.bytes_in,
            self.max_chunk_in,
            self.bytes_out,
            self.cost_usd(),
            phases.join(",")
        )
    }
}

/// RAII guard timing one backend call: records on drop.
pub struct BackendTimer {
    op: Op,
    start: f64,
}

impl BackendTimer {
    pub fn start(op: Op) -> BackendTimer {
        BackendTimer {
            op,
            start: now_ms(),
        }
    }
}

impl Drop for BackendTimer {
    fn drop(&mut self) {
        backend(self.op, now_ms() - self.start);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_and_takes() {
        begin();
        backend(Op::R2ClassB, 1.5);
        backend(Op::R2ClassB, 2.0);
        backend(Op::R2ClassA, 0.5);
        backend(Op::DoRequest, 3.0);
        phase("fetch: build pack", 7.0);
        add_bytes_in(10);
        add_bytes_in(4);
        add_bytes_out(20);
        let m = take().expect("metrics active");
        assert_eq!(m.r2_class_b, 2);
        assert_eq!(m.r2_class_a, 1);
        assert_eq!(m.do_requests, 1);
        assert!((m.backend_ms - 7.0).abs() < 1e-9);
        assert_eq!(m.phases, vec![("fetch: build pack", 7.0)]);
        assert_eq!((m.bytes_in, m.bytes_out), (14, 20));
        assert_eq!(m.max_chunk_in, 10);
        // Second take is empty; recording without begin is a no-op.
        assert!(take().is_none());
        backend(Op::Kv, 1.0);
        assert!(take().is_none());
    }

    #[test]
    fn server_timing_format() {
        begin();
        backend(Op::R2ClassB, 4.0);
        phase("push: stream+scan", 2.5);
        let m = take().unwrap();
        let h = m.server_timing(10.0);
        assert!(h.starts_with("total;dur=10.0"), "{h}");
        assert!(h.contains("backend;dur=4.0"), "{h}");
        assert!(h.contains("r2b;desc=\"1\""), "{h}");
        assert!(h.contains("push_stream_scan;dur=2.5"), "{h}");
        // Header value must be a single line of printable ASCII.
        assert!(h.bytes().all(|b| (0x20..0x7f).contains(&b)), "{h}");
    }

    #[test]
    fn log_json_is_valid_json() {
        begin();
        backend(Op::DoRequest, 1.0);
        phase("fetch: collect set", 3.25);
        let m = take().unwrap();
        let line = m.log_json("POST", "/r/git-upload-pack", 200, 12.5);
        let parsed: serde_json::Value = serde_json::from_str(&line).expect("valid json");
        assert_eq!(parsed["evt"], "req");
        assert_eq!(parsed["do"], 1);
        // Phase durations are serialized at 0.1 ms precision.
        assert_eq!(parsed["phases"]["fetch: collect set"], 3.2);
    }

    #[test]
    fn cost_model_matches_documented_prices() {
        let m = Metrics {
            r2_class_a: 1_000_000,
            r2_class_b: 1_000_000,
            do_requests: 1_000_000,
            kv_ops: 1_000_000,
            ..Default::default()
        };
        assert!((m.cost_usd() - (4.50 + 0.36 + 0.15 + 0.50)).abs() < 1e-9);
    }
}

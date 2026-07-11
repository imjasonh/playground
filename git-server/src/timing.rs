//! Pipeline phase timing.
//!
//! [`Phase`] is an RAII span guard: on drop it records the phase's duration
//! into the request-scoped metrics collector ([`crate::metrics`]) on every
//! target, and — natively, when the `GIT_SERVER_TIMING` environment variable
//! is set — also prints it to stderr for benchmark hotspot attribution.

use crate::metrics;

pub struct Phase {
    label: &'static str,
    start_ms: f64,
}

impl Phase {
    pub fn start(label: &'static str) -> Phase {
        Phase {
            label,
            start_ms: metrics::now_ms(),
        }
    }
}

impl Drop for Phase {
    fn drop(&mut self) {
        let elapsed_ms = metrics::now_ms() - self.start_ms;
        metrics::phase(self.label, elapsed_ms);
        // Mirror the phase onto the active Cloudflare custom span when one
        // is open (no-op natively / when unsampled).
        crate::trace::record_phase(self.label, elapsed_ms);
        #[cfg(not(target_arch = "wasm32"))]
        if std::env::var_os("GIT_SERVER_TIMING").is_some() {
            eprintln!("[timing] {:<28} {:>9.2}ms", self.label, elapsed_ms);
        }
    }
}

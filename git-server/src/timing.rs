//! Opt-in coarse phase timing for hotspot attribution.
//!
//! When the `GIT_SERVER_TIMING` environment variable is set (native builds
//! only — benchmarks and the test server), each instrumented pipeline phase
//! prints its wall time to stderr. No-op on wasm and when the variable is
//! unset, so production code paths carry no cost beyond a branch.

#[cfg(not(target_arch = "wasm32"))]
pub struct Phase {
    label: &'static str,
    start: Option<std::time::Instant>,
}

#[cfg(not(target_arch = "wasm32"))]
impl Phase {
    pub fn start(label: &'static str) -> Phase {
        let enabled = std::env::var_os("GIT_SERVER_TIMING").is_some();
        Phase {
            label,
            start: enabled.then(std::time::Instant::now),
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
impl Drop for Phase {
    fn drop(&mut self) {
        if let Some(start) = self.start {
            eprintln!("[timing] {:<28} {:>10.2?}", self.label, start.elapsed());
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub struct Phase;

#[cfg(target_arch = "wasm32")]
impl Phase {
    pub fn start(_label: &'static str) -> Phase {
        Phase
    }
}

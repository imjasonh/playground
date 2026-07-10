//! Heap tracking for tests and benchmarks (native only).
//!
//! Production runs in a Workers isolate with a **hard 128 MiB memory limit**;
//! exceeding it kills the request with Cloudflare error 1102 — and because
//! wasm linear memory never shrinks, one bloated request poisons the isolate
//! for every request after it. Native tests don't have that limit, which is
//! how a buffering bug can pass CI and 503 in production.
//!
//! [`TrackingAllocator`] closes that gap: test/bench binaries install it as
//! their `#[global_allocator]` and assert that peak live heap during a
//! request stays inside the isolate budget. It wraps the system allocator
//! with two atomics; overhead is negligible.
//!
//! ```ignore
//! #[global_allocator]
//! static ALLOC: git_server::memtrack::TrackingAllocator =
//!     git_server::memtrack::TrackingAllocator::new();
//!
//! memtrack::reset_peak();
//! // ... exercise the server ...
//! assert!(memtrack::peak_bytes() < memtrack::ISOLATE_BUDGET_BYTES);
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

/// The Workers isolate memory limit.
pub const ISOLATE_LIMIT_BYTES: usize = 128 * 1024 * 1024;

/// What a request may use of it in these tests: the isolate limit minus
/// headroom for the wasm module, runtime structures, and the JS copy of the
/// response body that the shim makes when relaying it (native tests can't
/// see that copy, so it's budgeted here instead).
pub const ISOLATE_BUDGET_BYTES: usize = 96 * 1024 * 1024;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

/// A system-allocator wrapper that tracks live and peak heap bytes.
pub struct TrackingAllocator;

impl TrackingAllocator {
    pub const fn new() -> Self {
        TrackingAllocator
    }
}

impl Default for TrackingAllocator {
    fn default() -> Self {
        Self::new()
    }
}

fn add(n: usize) {
    let live = LIVE.fetch_add(n, Ordering::Relaxed) + n;
    PEAK.fetch_max(live, Ordering::Relaxed);
}

fn sub(n: usize) {
    LIVE.fetch_sub(n, Ordering::Relaxed);
}

// SAFETY: delegates directly to `System`; the atomics only observe sizes.
unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = System.alloc(layout);
        if !p.is_null() {
            add(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
        sub(layout.size());
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = System.alloc_zeroed(layout);
        if !p.is_null() {
            add(layout.size());
        }
        p
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let p = System.realloc(ptr, layout, new_size);
        if !p.is_null() {
            sub(layout.size());
            add(new_size);
        }
        p
    }
}

/// Live heap bytes right now.
pub fn live_bytes() -> usize {
    LIVE.load(Ordering::Relaxed)
}

/// Peak live heap since the last [`reset_peak`].
pub fn peak_bytes() -> usize {
    PEAK.load(Ordering::Relaxed)
}

/// Reset the peak to the current live value (call before the phase you want
/// to measure).
pub fn reset_peak() {
    PEAK.store(LIVE.load(Ordering::Relaxed), Ordering::Relaxed);
}

/// Peak *additional* heap over the live level at the last reset — the
/// number to compare against a request budget.
pub fn peak_delta_since_reset(live_at_reset: usize) -> usize {
    peak_bytes().saturating_sub(live_at_reset)
}

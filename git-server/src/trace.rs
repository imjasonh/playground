//! Cloudflare Workers tracing facade.
//!
//! Production (wasm) opens custom spans via the `cloudflare:workers`
//! [`enterSpan`](https://developers.cloudflare.com/workers/observability/traces/custom-spans/)
//! API so application phases nest under the automatic platform spans (fetch
//! handler, R2, KV, Durable Object). Native builds are no-ops so the same
//! call sites compile in `cargo test`.
//!
//! Spans are **callback-scoped** (platform rule): there is no RAII start/end.
//! Pipeline [`crate::timing::Phase`] guards therefore attach their durations
//! as attributes on the active span via [`with_active_span`] rather than
//! opening a child span per phase.
//!
//! Enable with `[observability.traces] enabled = true` in `wrangler.toml`.

use std::cell::RefCell;

thread_local! {
    /// Innermost open custom span (wasm) or empty (native / unsampled).
    static ACTIVE: RefCell<Vec<ActiveSpan>> = const { RefCell::new(Vec::new()) };
    /// CF-Ray for the current request, if the edge supplied one.
    static RAY: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Handle to the currently open custom span (opaque on native).
#[derive(Clone)]
pub struct ActiveSpan {
    #[cfg(target_arch = "wasm32")]
    inner: wasm::Span,
}

impl ActiveSpan {
    /// Attach a string attribute when this request is being traced.
    pub fn set_attribute(&self, key: &str, value: &str) {
        #[cfg(target_arch = "wasm32")]
        self.inner.set_attribute_str(key, value);
        #[cfg(not(target_arch = "wasm32"))]
        let _ = (key, value);
    }

    /// Attach a numeric attribute (JS `number`).
    pub fn set_attribute_f64(&self, key: &str, value: f64) {
        #[cfg(target_arch = "wasm32")]
        self.inner.set_attribute_num(key, value);
        #[cfg(not(target_arch = "wasm32"))]
        let _ = (key, value);
    }

    /// Whether the platform is recording this span (head sampling).
    pub fn is_traced(&self) -> bool {
        #[cfg(target_arch = "wasm32")]
        {
            self.inner.is_traced()
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            false
        }
    }
}

/// Record the CF-Ray (or clear it) for the current request. Cleared by
/// [`crate::metrics::begin`].
pub fn set_ray(ray: Option<String>) {
    RAY.with(|r| *r.borrow_mut() = ray);
}

/// CF-Ray for the current request, if known.
pub fn ray() -> Option<String> {
    RAY.with(|r| r.borrow().clone())
}

pub(crate) fn clear_ray() {
    RAY.with(|r| *r.borrow_mut() = None);
}

/// Run `f` with the innermost open custom span, if any.
pub fn with_active_span<R>(f: impl FnOnce(&ActiveSpan) -> R) -> Option<R> {
    ACTIVE.with(|stack| stack.borrow().last().map(f))
}

fn push_active(span: ActiveSpan) {
    ACTIVE.with(|s| s.borrow_mut().push(span));
}

fn pop_active() {
    ACTIVE.with(|s| {
        s.borrow_mut().pop();
    });
}

/// Record a completed pipeline phase on the active custom span (no-op when
/// nothing is open or the request is not sampled).
pub fn record_phase(label: &str, ms: f64) {
    with_active_span(|span| {
        if !span.is_traced() {
            return;
        }
        // Attribute keys must be reasonably token-like for OTel exporters.
        let key: String = label
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect::<String>()
            .split('_')
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .join("_");
        span.set_attribute_f64(&format!("git.phase.{key}_ms"), ms);
    });
}

/// Open an async custom span around `f`. On native this still pushes a
/// no-op [`ActiveSpan`] so [`with_active_span`] / [`record_phase`] see a
/// stack; on wasm it calls `cloudflare:workers` `tracing.enterSpan`.
///
/// `name` and the future must be `'static` because the platform keeps the
/// span open until the returned promise settles.
#[cfg(target_arch = "wasm32")]
pub async fn span_async<F, Fut, T>(name: &'static str, f: F) -> T
where
    F: FnOnce(ActiveSpan) -> Fut + 'static,
    Fut: std::future::Future<Output = T> + 'static,
    T: 'static,
{
    wasm::enter_span_async(name, f).await
}

#[cfg(not(target_arch = "wasm32"))]
pub async fn span_async<F, Fut, T>(_name: &'static str, f: F) -> T
where
    F: FnOnce(ActiveSpan) -> Fut,
    Fut: std::future::Future<Output = T>,
{
    let span = ActiveSpan {};
    push_active(span.clone());
    let out = f(span).await;
    pop_active();
    out
}

#[cfg(target_arch = "wasm32")]
mod wasm {
    use super::{pop_active, push_active, ActiveSpan};
    use js_sys::Promise;
    use std::cell::RefCell;
    use std::future::Future;
    use std::rc::Rc;
    use wasm_bindgen::prelude::*;
    use wasm_bindgen_futures::{future_to_promise, JsFuture};

    #[wasm_bindgen(module = "cloudflare:workers")]
    extern "C" {
        /// The `tracing` export from `cloudflare:workers`.
        #[wasm_bindgen(thread_local_v2, js_name = tracing)]
        static TRACING: Tracing;

        type Tracing;

        #[wasm_bindgen(method, js_name = enterSpan)]
        fn enter_span_async(
            this: &Tracing,
            name: &str,
            cb: &Closure<dyn FnMut(Span) -> Promise>,
        ) -> Promise;

        #[wasm_bindgen(js_name = Span)]
        #[derive(Clone)]
        pub type Span;

        #[wasm_bindgen(method, js_name = setAttribute)]
        pub fn set_attribute_str(this: &Span, key: &str, value: &str);

        #[wasm_bindgen(method, js_name = setAttribute)]
        pub fn set_attribute_num(this: &Span, key: &str, value: f64);

        #[wasm_bindgen(method, getter, js_name = isTraced)]
        pub fn is_traced(this: &Span) -> bool;
    }

    pub async fn enter_span_async<F, Fut, T>(name: &str, f: F) -> T
    where
        F: FnOnce(ActiveSpan) -> Fut + 'static,
        Fut: Future<Output = T> + 'static,
        T: 'static,
    {
        let result: Rc<RefCell<Option<T>>> = Rc::new(RefCell::new(None));
        let sink = result.clone();
        let mut f = Some(f);

        let cb = Closure::wrap(Box::new(move |span: Span| -> Promise {
            let span = ActiveSpan { inner: span };
            let f = f.take().expect("enterSpan invoked its callback twice");
            let fut = f(span.clone());
            let sink = sink.clone();
            future_to_promise(async move {
                push_active(span);
                let value = fut.await;
                pop_active();
                *sink.borrow_mut() = Some(value);
                Ok(JsValue::UNDEFINED)
            })
        }) as Box<dyn FnMut(Span) -> Promise>);

        let promise = TRACING.with(|t| t.enter_span_async(name, &cb));
        let _ = JsFuture::from(promise).await;
        drop(cb);

        Rc::try_unwrap(result)
            .ok()
            .expect("span future outlived its handle")
            .into_inner()
            .expect("enterSpan async callback must resolve the result")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ray_roundtrip() {
        clear_ray();
        assert!(ray().is_none());
        set_ray(Some("abc-SJC".into()));
        assert_eq!(ray().as_deref(), Some("abc-SJC"));
        clear_ray();
        assert!(ray().is_none());
    }

    #[test]
    fn native_span_async_runs_body() {
        let n = futures::executor::block_on(span_async("test", |_span| async { 7u32 }));
        assert_eq!(n, 7);
    }
}

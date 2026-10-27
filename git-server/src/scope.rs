//! Per-request context on an isolate that interleaves requests.
//!
//! One Workers isolate polls many requests' futures on a single thread, so a
//! plain `thread_local!` stack is shared by every request in flight. One
//! request's pop can then remove another's frame, and a later phase record
//! calls a span the platform has already ended. A [`Frame`] holds one
//! request's metrics, spans, and CF-Ray. [`Scoped`] installs that frame only
//! while that request's future is being polled.

use std::cell::RefCell;
#[cfg(any(test, target_arch = "wasm32"))]
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll};

use futures::Stream;

use crate::metrics::Metrics;
use crate::trace::ActiveSpan;

/// One request's context.
#[derive(Default)]
pub(crate) struct Frame {
    pub(crate) metrics: Vec<Metrics>,
    pub(crate) spans: Vec<ActiveSpan>,
    pub(crate) ray: Option<String>,
}

/// Shared handle to a [`Frame`].
pub(crate) type Handle = Rc<RefCell<Frame>>;

thread_local! {
    /// The frame of the future being polled. Code that runs outside any
    /// [`Scoped`] future (native tests, Durable Object calls) uses one root
    /// frame per thread.
    static CURRENT: RefCell<Handle> = RefCell::new(Rc::default());
}

/// A new, empty frame. Fetch, the background repack, and cron each start on
/// one of these. Native code other than tests stays on the root frame.
#[cfg(any(test, target_arch = "wasm32"))]
pub(crate) fn fresh() -> Handle {
    Rc::default()
}

/// The frame of the future being polled.
pub(crate) fn current() -> Handle {
    CURRENT.with(|c| c.borrow().clone())
}

/// Run `f` on the current frame. `f` must not call back into this module.
pub(crate) fn with<R>(f: impl FnOnce(&mut Frame) -> R) -> R {
    let frame = current();
    let mut frame = frame.borrow_mut();
    f(&mut frame)
}

fn enter(frame: &Handle) -> Handle {
    CURRENT.with(|c| c.replace(frame.clone()))
}

fn leave(prev: Handle) {
    CURRENT.with(|c| *c.borrow_mut() = prev);
}

/// A future that runs with `frame` as the current frame.
#[cfg(any(test, target_arch = "wasm32"))]
pub(crate) struct Scoped<F> {
    frame: Handle,
    inner: Pin<Box<F>>,
}

/// Poll `fut` with `frame` as the current frame.
#[cfg(any(test, target_arch = "wasm32"))]
pub(crate) fn run<F: Future>(frame: Handle, fut: F) -> Scoped<F> {
    Scoped {
        frame,
        inner: Box::pin(fut),
    }
}

#[cfg(any(test, target_arch = "wasm32"))]
impl<F: Future> Future for Scoped<F> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<F::Output> {
        let this = &mut *self;
        let prev = enter(&this.frame);
        let out = this.inner.as_mut().poll(cx);
        leave(prev);
        out
    }
}

/// A stream that runs with `frame` as the current frame.
pub(crate) struct ScopedStream<S> {
    frame: Handle,
    inner: Pin<Box<S>>,
}

/// Poll `stream` with `frame` as the current frame. A streamed response body
/// keeps running after the handler returns, so it carries its frame along.
pub(crate) fn stream<S: Stream>(frame: Handle, stream: S) -> ScopedStream<S> {
    ScopedStream {
        frame,
        inner: Box::pin(stream),
    }
}

impl<S: Stream> Stream for ScopedStream<S> {
    type Item = S::Item;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<S::Item>> {
        let this = &mut *self;
        let prev = enter(&this.frame);
        let out = this.inner.as_mut().poll_next(cx);
        leave(prev);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::future::join;
    use futures::task::noop_waker;

    /// Two interleaved requests each see only their own frame.
    #[test]
    fn interleaved_futures_keep_their_frames() {
        let (tx_a, rx_a) = futures::channel::oneshot::channel::<()>();
        let (tx_b, rx_b) = futures::channel::oneshot::channel::<()>();
        let a = run(fresh(), async move {
            with(|f| f.ray = Some("a".into()));
            rx_a.await.unwrap();
            with(|f| f.ray.clone())
        });
        let b = run(fresh(), async move {
            with(|f| f.ray = Some("b".into()));
            rx_b.await.unwrap();
            with(|f| f.ray.clone())
        });
        let mut both = Box::pin(join(a, b));
        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        assert!(both.as_mut().poll(&mut cx).is_pending());
        tx_a.send(()).unwrap();
        tx_b.send(()).unwrap();
        match both.as_mut().poll(&mut cx) {
            Poll::Ready((ra, rb)) => {
                assert_eq!(ra.as_deref(), Some("a"));
                assert_eq!(rb.as_deref(), Some("b"));
            }
            Poll::Pending => panic!("both futures should be ready"),
        }
        assert!(with(|f| f.ray.is_none()), "root frame untouched");
    }
}

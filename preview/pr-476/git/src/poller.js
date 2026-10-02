/**
 * A small, visibility-aware polling scheduler.
 *
 * It calls an async `onPoll` callback on a fixed interval while the poller is
 * running *and* the document is visible. When the tab is hidden it pauses
 * automatically (a background tab never hits the network on our behalf) and
 * resumes — with one immediate catch-up tick — when the tab becomes visible
 * again. Overlapping ticks are suppressed: if the previous `onPoll` is still in
 * flight when the next interval fires, that tick is skipped, so a slow check can
 * never stack up.
 *
 * The git app uses this to peek at the upstream for new commits and auto-fetch
 * them (see `pollForUpdates` in controller.js), but nothing here is git-aware.
 *
 * Timers and the visibility source are injectable so the scheduler is fully
 * unit-testable without real time or a DOM.
 */

/** Default gap between upstream checks. Conservative to be easy on the proxy. */
export const DEFAULT_POLL_INTERVAL_MS = 60000;

/**
 * @param {Object} options
 * @param {() => (void | Promise<void>)} options.onPoll  called each live tick
 * @param {number} [options.intervalMs]
 * @param {(fn: Function, ms: number) => any} [options.setInterval]
 * @param {(id: any) => void} [options.clearInterval]
 * @param {?{hidden: boolean, addEventListener: Function, removeEventListener: Function}} [options.doc]
 *   visibility source; defaults to `document`, or `null` in a non-DOM host
 *   (where the poller treats itself as always visible)
 * @returns {{ start: () => void, stop: () => void, isRunning: () => boolean }}
 */
export function createUpdatePoller(options) {
  const onPoll = options.onPoll;
  const intervalMs = options.intervalMs || DEFAULT_POLL_INTERVAL_MS;
  // Wrap the global timers in arrows so a bound `this` is never required (some
  // environments throw "Illegal invocation" on a detached setInterval).
  const setIntervalFn =
    options.setInterval || ((fn, ms) => globalThis.setInterval(fn, ms));
  const clearIntervalFn =
    options.clearInterval || ((id) => globalThis.clearInterval(id));
  const doc =
    options.doc !== undefined
      ? options.doc
      : typeof document !== 'undefined'
        ? document
        : null;

  let running = false;
  let timerId = null;
  let inFlight = false;

  function isHidden() {
    return Boolean(doc && doc.hidden);
  }

  function schedule() {
    if (timerId !== null) return;
    timerId = setIntervalFn(() => {
      void runTick();
    }, intervalMs);
  }

  function unschedule() {
    if (timerId === null) return;
    clearIntervalFn(timerId);
    timerId = null;
  }

  /** Run one tick unless hidden or a previous tick is still in flight. */
  async function runTick() {
    if (!running || inFlight || isHidden()) return;
    inFlight = true;
    try {
      await onPoll();
    } catch {
      // The scheduler must survive a failing tick and keep polling; the
      // callback owns its own error reporting (here we stay silent).
    } finally {
      inFlight = false;
    }
  }

  function onVisibilityChange() {
    if (!running) return;
    if (isHidden()) {
      unschedule();
    } else {
      // Became visible: resume the interval and check once immediately so a
      // user returning to the tab sees fresh state without waiting a full cycle.
      schedule();
      void runTick();
    }
  }

  function start() {
    if (running) return;
    running = true;
    if (doc && typeof doc.addEventListener === 'function') {
      doc.addEventListener('visibilitychange', onVisibilityChange);
    }
    if (!isHidden()) schedule();
  }

  function stop() {
    if (!running) return;
    running = false;
    unschedule();
    if (doc && typeof doc.removeEventListener === 'function') {
      doc.removeEventListener('visibilitychange', onVisibilityChange);
    }
  }

  return {
    start,
    stop,
    isRunning: () => running,
  };
}

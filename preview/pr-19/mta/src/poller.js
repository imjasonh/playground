/**
 * A small, visibility-aware polling scheduler for live refreshes.
 *
 * It runs `onPoll` on a fixed interval while running *and* the tab is visible,
 * pauses when the tab is hidden (no background network), and does one immediate
 * catch-up tick when the tab returns. Overlapping ticks are suppressed so a slow
 * refresh never stacks up. Timers and the visibility source are injectable for
 * tests. (Same shape as the git app's poller — a proven pattern.)
 */

export const DEFAULT_INTERVAL_MS = 30000;

/**
 * @param {{
 *   onPoll: () => (void | Promise<void>),
 *   intervalMs?: number,
 *   setInterval?: (fn: Function, ms: number) => any,
 *   clearInterval?: (id: any) => void,
 *   doc?: ?{hidden: boolean, addEventListener: Function, removeEventListener: Function},
 * }} options
 */
export function createPoller(options) {
  const onPoll = options.onPoll;
  const intervalMs = options.intervalMs || DEFAULT_INTERVAL_MS;
  const setIntervalFn = options.setInterval || ((fn, ms) => globalThis.setInterval(fn, ms));
  const clearIntervalFn = options.clearInterval || ((id) => globalThis.clearInterval(id));
  const doc = options.doc !== undefined ? options.doc : typeof document !== 'undefined' ? document : null;

  let running = false;
  let timerId = null;
  let inFlight = false;

  const isHidden = () => Boolean(doc && doc.hidden);

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

  async function runTick() {
    if (!running || inFlight || isHidden()) return;
    inFlight = true;
    try {
      await onPoll();
    } catch {
      // Keep polling through a failed tick; the callback owns error reporting.
    } finally {
      inFlight = false;
    }
  }

  function onVisibilityChange() {
    if (!running) return;
    if (isHidden()) {
      unschedule();
    } else {
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

  return { start, stop, isRunning: () => running };
}

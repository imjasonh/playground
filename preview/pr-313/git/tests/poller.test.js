import { createUpdatePoller, DEFAULT_POLL_INTERVAL_MS } from '../src/poller.js';

/** Let queued microtasks/macrotasks settle (onPoll is async). */
const flush = () => new Promise((resolve) => setTimeout(resolve, 0));

/** A deferred so a test can hold a tick "in flight" deterministically. */
function deferred() {
  let resolve;
  const promise = new Promise((r) => {
    resolve = r;
  });
  return { promise, resolve };
}

/** A fake interval timer the test fires by hand (no real time involved). */
function fakeTimers() {
  let nextId = 1;
  const intervals = new Map();
  let lastMs = null;
  return {
    setInterval: (fn, ms) => {
      lastMs = ms;
      const id = nextId++;
      intervals.set(id, fn);
      return id;
    },
    clearInterval: (id) => {
      intervals.delete(id);
    },
    fireAll: () => {
      for (const fn of [...intervals.values()]) fn();
    },
    count: () => intervals.size,
    lastMs: () => lastMs,
  };
}

/** A minimal visibility source the test drives via `hidden` + `emit`. */
function fakeDoc() {
  const listeners = new Map();
  return {
    hidden: false,
    addEventListener(type, cb) {
      if (!listeners.has(type)) listeners.set(type, new Set());
      listeners.get(type).add(cb);
    },
    removeEventListener(type, cb) {
      const set = listeners.get(type);
      if (set) set.delete(cb);
    },
    emit(type) {
      for (const cb of [...(listeners.get(type) || [])]) cb();
    },
    listenerCount(type) {
      const set = listeners.get(type);
      return set ? set.size : 0;
    },
  };
}

function makePoller(onPoll, { doc, intervalMs } = {}) {
  const timers = fakeTimers();
  const poller = createUpdatePoller({
    onPoll,
    intervalMs,
    setInterval: timers.setInterval,
    clearInterval: timers.clearInterval,
    doc,
  });
  return { poller, timers };
}

describe('createUpdatePoller', () => {
  test('ticks on each interval while running and visible', async () => {
    let calls = 0;
    const { poller, timers } = makePoller(() => {
      calls += 1;
    }, { doc: fakeDoc() });

    poller.start();
    expect(poller.isRunning()).toBe(true);
    expect(timers.count()).toBe(1);

    timers.fireAll();
    await flush();
    expect(calls).toBe(1);

    timers.fireAll();
    await flush();
    expect(calls).toBe(2);
  });

  test('uses the default interval, or an explicit one', () => {
    const a = makePoller(() => {}, { doc: fakeDoc() });
    a.poller.start();
    expect(a.timers.lastMs()).toBe(DEFAULT_POLL_INTERVAL_MS);

    const b = makePoller(() => {}, { doc: fakeDoc(), intervalMs: 5000 });
    b.poller.start();
    expect(b.timers.lastMs()).toBe(5000);
  });

  test('stop() clears the interval and prevents further ticks', async () => {
    let calls = 0;
    const { poller, timers } = makePoller(() => {
      calls += 1;
    }, { doc: fakeDoc() });

    poller.start();
    timers.fireAll();
    await flush();
    expect(calls).toBe(1);

    poller.stop();
    expect(poller.isRunning()).toBe(false);
    expect(timers.count()).toBe(0);

    timers.fireAll(); // nothing is scheduled anymore
    await flush();
    expect(calls).toBe(1);
  });

  test('start() is idempotent (single interval and listener)', () => {
    const doc = fakeDoc();
    const { poller, timers } = makePoller(() => {}, { doc });
    poller.start();
    poller.start();
    expect(timers.count()).toBe(1);
    expect(doc.listenerCount('visibilitychange')).toBe(1);

    poller.stop();
    expect(doc.listenerCount('visibilitychange')).toBe(0);
  });

  test('does not poll while hidden, and resumes with a catch-up tick', async () => {
    let calls = 0;
    const doc = fakeDoc();
    doc.hidden = true;
    const { poller, timers } = makePoller(() => {
      calls += 1;
    }, { doc });

    poller.start();
    // Hidden at start: running, but no interval scheduled and no tick.
    expect(poller.isRunning()).toBe(true);
    expect(timers.count()).toBe(0);
    timers.fireAll();
    await flush();
    expect(calls).toBe(0);

    // Becoming visible resumes the interval and checks once immediately.
    doc.hidden = false;
    doc.emit('visibilitychange');
    await flush();
    expect(timers.count()).toBe(1);
    expect(calls).toBe(1);
  });

  test('pauses polling when the tab becomes hidden', async () => {
    let calls = 0;
    const doc = fakeDoc();
    const { poller, timers } = makePoller(() => {
      calls += 1;
    }, { doc });

    poller.start();
    expect(timers.count()).toBe(1);

    doc.hidden = true;
    doc.emit('visibilitychange');
    expect(timers.count()).toBe(0);

    timers.fireAll();
    await flush();
    expect(calls).toBe(0);
  });

  test('skips overlapping ticks until the previous one settles', async () => {
    let starts = 0;
    let gate = deferred();
    const { poller, timers } = makePoller(async () => {
      starts += 1;
      await gate.promise;
    }, { doc: fakeDoc() });

    poller.start();
    timers.fireAll(); // tick 1 begins, stays in flight
    await flush();
    expect(starts).toBe(1);

    timers.fireAll(); // suppressed: tick 1 is still running
    await flush();
    expect(starts).toBe(1);

    gate.resolve(); // tick 1 completes
    await flush();
    gate = deferred();

    timers.fireAll(); // now idle, so this one runs
    await flush();
    expect(starts).toBe(2);
  });

  test('keeps polling even if a tick throws', async () => {
    let calls = 0;
    const { poller, timers } = makePoller(async () => {
      calls += 1;
      throw new Error('peek failed');
    }, { doc: fakeDoc() });

    poller.start();
    timers.fireAll();
    await flush();
    timers.fireAll();
    await flush();
    expect(calls).toBe(2); // the thrown error didn't stop the scheduler
  });

  test('works without a visibility source (always considered visible)', async () => {
    let calls = 0;
    const { poller, timers } = makePoller(() => {
      calls += 1;
    }, { doc: null });

    poller.start();
    expect(timers.count()).toBe(1);
    timers.fireAll();
    await flush();
    expect(calls).toBe(1);
    poller.stop();
  });
});

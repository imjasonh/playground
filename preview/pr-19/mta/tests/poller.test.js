import { createPoller } from '../src/poller.js';

function harness() {
  const ctx = { intervalFn: null, cleared: 0, visHandler: null };
  const doc = {
    hidden: false,
    addEventListener: (type, handler) => {
      if (type === 'visibilitychange') ctx.visHandler = handler;
    },
    removeEventListener: () => {},
  };
  const setInterval = (fn) => {
    ctx.intervalFn = fn;
    return 1;
  };
  const clearInterval = () => {
    ctx.cleared += 1;
    ctx.intervalFn = null;
  };
  return { ctx, doc, setInterval, clearInterval };
}

const flush = () => new Promise((resolve) => setTimeout(resolve, 0));

describe('createPoller', () => {
  test('start schedules and ticks call onPoll', async () => {
    const { ctx, doc, setInterval, clearInterval } = harness();
    let calls = 0;
    const poller = createPoller({ onPoll: () => { calls += 1; }, setInterval, clearInterval, doc });
    poller.start();
    expect(poller.isRunning()).toBe(true);
    expect(typeof ctx.intervalFn).toBe('function');

    ctx.intervalFn();
    await flush();
    expect(calls).toBe(1);
  });

  test('suppresses overlapping ticks', async () => {
    const { ctx, doc, setInterval, clearInterval } = harness();
    let calls = 0;
    let release;
    const onPoll = () => {
      calls += 1;
      return new Promise((resolve) => { release = resolve; });
    };
    const poller = createPoller({ onPoll, setInterval, clearInterval, doc });
    poller.start();

    ctx.intervalFn(); // starts an in-flight tick
    ctx.intervalFn(); // skipped while the first is pending
    expect(calls).toBe(1);

    release();
    await flush();
    ctx.intervalFn(); // now allowed again
    await flush();
    expect(calls).toBe(2);
  });

  test('pauses when hidden and catches up when visible', async () => {
    const { ctx, doc, setInterval, clearInterval } = harness();
    let calls = 0;
    const poller = createPoller({ onPoll: () => { calls += 1; }, setInterval, clearInterval, doc });
    poller.start();

    doc.hidden = true;
    ctx.visHandler();
    expect(ctx.cleared).toBeGreaterThan(0);
    expect(ctx.intervalFn).toBeNull();

    doc.hidden = false;
    ctx.visHandler(); // reschedules + immediate catch-up tick
    await flush();
    expect(typeof ctx.intervalFn).toBe('function');
    expect(calls).toBe(1);
  });

  test('stop halts polling', () => {
    const { ctx, doc, setInterval, clearInterval } = harness();
    const poller = createPoller({ onPoll: () => {}, setInterval, clearInterval, doc });
    poller.start();
    poller.stop();
    expect(poller.isRunning()).toBe(false);
    expect(ctx.intervalFn).toBeNull();
  });
});

import { createStore, createLoadController } from '../src/store.js';

describe('createStore', () => {
  test('getState returns the initial state', () => {
    const store = createStore({ a: 1, b: 'two' });
    expect(store.getState()).toEqual({ a: 1, b: 'two' });
  });

  test('setState shallow-merges and notifies subscribers', () => {
    const store = createStore({ a: 1, b: 2 });
    const seen = [];
    store.subscribe((s) => seen.push({ ...s }));
    store.setState({ b: 20 });
    expect(store.getState()).toEqual({ a: 1, b: 20 });
    expect(seen).toEqual([{ a: 1, b: 20 }]);
  });

  test('update mutates in place (e.g. a Set) and notifies', () => {
    const store = createStore({ expanded: new Set() });
    let calls = 0;
    store.subscribe(() => (calls += 1));
    store.update((s) => s.expanded.add('src'));
    expect([...store.getState().expanded]).toEqual(['src']);
    expect(calls).toBe(1);
  });

  test('subscribe returns an unsubscribe', () => {
    const store = createStore({ n: 0 });
    let calls = 0;
    const off = store.subscribe(() => (calls += 1));
    store.setState({ n: 1 });
    off();
    store.setState({ n: 2 });
    expect(calls).toBe(1);
  });

  test('select fires only when the slice changes and passes prev/next', () => {
    const store = createStore({ ref: 'main', other: 0 });
    const changes = [];
    store.select(
      (s) => s.ref,
      (next, prev) => changes.push([prev, next])
    );
    store.setState({ other: 1 }); // ref unchanged -> no fire
    store.setState({ ref: 'dev' }); // -> fire
    store.setState({ ref: 'dev' }); // same value -> no fire
    expect(changes).toEqual([['main', 'dev']]);
  });

  test('coalesces re-entrant notifications into a settled round', () => {
    const store = createStore({ a: 0, b: 0 });
    const order = [];
    // A listener that reacts to `a` by bumping `b` once.
    store.subscribe((s) => {
      if (s.a === 1 && s.b === 0) store.setState({ b: 1 });
    });
    store.subscribe((s) => order.push(`${s.a}:${s.b}`));
    store.setState({ a: 1 });
    // The observing listener should end up seeing the settled a:1,b:1 state.
    expect(order[order.length - 1]).toBe('1:1');
  });
});

describe('createLoadController', () => {
  test('begin supersedes the previous load', () => {
    const loads = createLoadController();
    const first = loads.begin();
    expect(first.active).toBe(true);
    const second = loads.begin();
    expect(first.active).toBe(false);
    expect(second.active).toBe(true);
    expect(loads.current).toBe(2);
  });

  test('cancel invalidates in-flight loads without starting a new active one', () => {
    const loads = createLoadController();
    const load = loads.begin();
    expect(load.active).toBe(true);
    loads.cancel();
    expect(load.active).toBe(false);
  });
});

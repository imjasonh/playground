/**
 * A tiny observable store and a first-class "current load" controller.
 *
 * The app used to keep a bare `state` object that every module mutated in place,
 * plus a hand-incremented `loadToken` integer to guard against out-of-order
 * async loads. Both are centralized here:
 *
 *   - `createStore` funnels mutations through `setState` / `update` and notifies
 *     subscribers, so cross-cutting concerns (e.g. syncing the URL hash) can
 *     react to state changes instead of being wired in imperatively.
 *   - `createLoadController` turns the load token into a small handle with an
 *     `active` flag, so async flows read `load.active` after each await instead
 *     of comparing a captured integer against a module global.
 *
 * Reads still go through a single live state object (returned by `getState`) so
 * the migration stays small; the win is that every *write* now flows through one
 * observable choke point.
 */

/**
 * @template {object} T
 * @param {T} [initial]
 * @returns {{
 *   getState: () => T,
 *   setState: (patch: Partial<T>) => T,
 *   update: (mutator: (state: T) => void) => T,
 *   subscribe: (listener: (state: T) => void) => () => void,
 *   select: <V>(selector: (state: T) => V, listener: (next: V, prev: V) => void) => () => void,
 * }}
 */
export function createStore(initial = {}) {
  const state = { ...initial };
  const listeners = new Set();
  let notifying = 0;
  let dirty = false;

  const getState = () => state;

  function notify() {
    // Coalesce notifications raised re-entrantly (a listener that triggers
    // another mutation) into one more pass, so subscribers see a settled state.
    if (notifying > 0) {
      dirty = true;
      return;
    }
    notifying += 1;
    try {
      do {
        dirty = false;
        for (const listener of [...listeners]) listener(state);
      } while (dirty);
    } finally {
      notifying -= 1;
    }
  }

  function setState(patch) {
    if (patch) Object.assign(state, patch);
    notify();
    return state;
  }

  function update(mutator) {
    mutator(state);
    notify();
    return state;
  }

  function subscribe(listener) {
    listeners.add(listener);
    return () => listeners.delete(listener);
  }

  function select(selector, listener) {
    let prev = selector(state);
    return subscribe(() => {
      const next = selector(state);
      if (!Object.is(next, prev)) {
        const old = prev;
        prev = next;
        listener(next, old);
      }
    });
  }

  return { getState, setState, update, subscribe, select };
}

/**
 * Monotonic "current load" tracker. Each `begin()` supersedes the previous load;
 * the returned handle's `active` flag is true only while it is the most recent
 * one, so an interleaved async flow can bail right after an await.
 *
 * @returns {{ begin: () => {id: number, active: boolean}, cancel: () => void, current: number }}
 */
export function createLoadController() {
  let current = 0;
  return {
    begin() {
      const id = (current += 1);
      return {
        id,
        get active() {
          return id === current;
        },
      };
    },
    /** Invalidate every in-flight load without starting a new one. */
    cancel() {
      current += 1;
    },
    get current() {
      return current;
    },
  };
}

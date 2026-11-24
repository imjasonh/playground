/** Test doubles for timers and the Web Speech API. */

/** A clock that only moves when a test calls `tick`. */
export class FakeTimer {
  constructor() {
    this.now = 0;
    this.nextId = 1;
    /** @type {!Map<number, {at: number, fn: Function, every: number}>} */
    this.tasks = new Map();
  }

  setTimeout(fn, ms = 0) {
    const id = this.nextId++;
    this.tasks.set(id, {at: this.now + ms, fn, every: 0});
    return id;
  }

  clearTimeout(id) {
    this.tasks.delete(id);
  }

  setInterval(fn, ms) {
    const id = this.nextId++;
    this.tasks.set(id, {at: this.now + ms, fn, every: ms});
    return id;
  }

  clearInterval(id) {
    this.tasks.delete(id);
  }

  /** Runs every task due within the next `ms` milliseconds, in order. */
  tick(ms) {
    const end = this.now + ms;
    for (;;) {
      let next = null;
      for (const [id, t] of this.tasks) {
        if (t.at <= end && (!next || t.at < next[1].at)) next = [id, t];
      }
      if (!next) break;
      const [id, t] = next;
      this.now = t.at;
      if (t.every) {
        t.at += t.every;
      } else {
        this.tasks.delete(id);
      }
      t.fn();
    }
    this.now = end;
  }

  get pending() {
    return this.tasks.size;
  }
}

export class FakeUtterance {
  constructor(text) {
    this.text = text;
    this.rate = 1;
    this.lang = '';
    this.voice = null;
    this.onend = null;
    this.onerror = null;
    this.onboundary = null;
  }
}

/**
 * Records utterances. Tests finish or fail the current one by hand. Like
 * Chrome, `cancel` fires `interrupted` on the utterance it drops.
 */
export class FakeSynth {
  constructor() {
    /** @type {!Array<!FakeUtterance>} */
    this.spoken = [];
    this.current = null;
    this.speaking = false;
    this.paused = false;
    this.pauses = 0;
  }

  speak(u) {
    this.spoken.push(u);
    this.current = u;
    this.speaking = true;
  }

  cancel() {
    const u = this.current;
    this.current = null;
    this.speaking = false;
    u?.onerror?.({error: 'interrupted'});
  }

  pause() {
    this.paused = true;
    this.pauses++;
  }

  resume() {
    this.paused = false;
  }

  /** Ends the current utterance normally. */
  finish() {
    const u = this.current;
    this.current = null;
    this.speaking = false;
    u.onend?.({});
  }

  /** @param {string} error */
  fail(error) {
    const u = this.current;
    this.current = null;
    this.speaking = false;
    u.onerror?.({error});
  }

  /** @return {!Array<string>} */
  get texts() {
    return this.spoken.map((u) => u.text);
  }
}

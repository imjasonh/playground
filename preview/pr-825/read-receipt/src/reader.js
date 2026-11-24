// Tracks progress through a doc one word at a time.

/**
 * Reports whether a keydown is a step key: Right Arrow or Space, without a
 * modifier, so shortcuts keep working. A held key's repeats match too.
 * @param {{key: string, altKey: boolean, ctrlKey: boolean, metaKey: boolean,
 *     shiftKey: boolean}} event
 * @return {boolean}
 */
export function isStepKey(event) {
  if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) {
    return false;
  }
  return event.key === 'ArrowRight' || event.key === ' ';
}

/** The fastest pace a reader can step through a doc, in words per minute. */
export const MAX_WPM = 400;

/**
 * How many words a reader can step through at once before the pace limit
 * applies, so a quick "of the" doesn't stall.
 */
const BURST = 5;

const WORDS_PER_MS = MAX_WPM / 60_000;

/**
 * Reports whether a reader could step through `total` words in `seconds`,
 * rounded to the nearest second, under `MAX_WPM`.
 * @param {number} total
 * @param {number} seconds
 * @return {boolean}
 */
export function withinSpeedLimit(total, seconds) {
  return total <= BURST + (seconds + 0.5) * 1000 * WORDS_PER_MS;
}

/**
 * @param {number} total
 * @param {number} seconds
 * @return {?number} Words per minute, or null when `seconds` is 0.
 */
export function wordsPerMinute(total, seconds) {
  return seconds ? Math.round((total * 60) / seconds) : null;
}

/**
 * Steps through `total` words, no faster than `MAX_WPM` after the first
 * `BURST`. The clock starts at the first step.
 */
export class Reader {
  /**
   * @param {number} total
   * @param {function(): number=} now Milliseconds since the epoch.
   */
  constructor(total, now = Date.now) {
    /** @private @const */
    this.total_ = total;
    /** @private @const */
    this.now_ = now;
    /** @private */
    this.index_ = 0;
    /** @private {?number} */
    this.startedAt_ = null;
    /** @private {?number} */
    this.steppedAt_ = null;
    /** @private Steps allowed right away, as of `steppedAt_`. */
    this.allowance_ = BURST;
  }

  /** @return {number} The index of the word to click next. */
  get index() {
    return this.index_;
  }

  /** @return {number} */
  get total() {
    return this.total_;
  }

  /** @return {boolean} Whether every word has been read. */
  get done() {
    return this.index_ >= this.total_;
  }

  /**
   * Marks the current word read, unless the doc is done or the step comes
   * sooner than `MAX_WPM` allows.
   * @return {boolean} Whether the reader moved.
   */
  advance() {
    if (this.done) return false;
    const now = this.now_();
    const earned =
      this.steppedAt_ === null ? 0 : (now - this.steppedAt_) * WORDS_PER_MS;
    const allowance = Math.min(BURST, this.allowance_ + earned);
    if (allowance < 1) return false;
    this.allowance_ = allowance - 1;
    this.steppedAt_ = now;
    this.startedAt_ ??= now;
    this.index_++;
    return true;
  }

  /**
   * @return {?number} When the last word was read, in ms since the epoch, or
   *     null until then.
   */
  get finishedAt() {
    return this.done ? this.steppedAt_ : null;
  }

  /** @return {number} Whole seconds from the first step to the latest. */
  get seconds() {
    if (this.startedAt_ === null || this.steppedAt_ === null) return 0;
    return Math.round((this.steppedAt_ - this.startedAt_) / 1000);
  }
}

/**
 * Formats a duration as hours, minutes, and seconds, dropping leading zero
 * units: `42s`, `4m 12s`, `1h 0m 5s`.
 * @param {number} seconds
 * @return {string}
 */
export function formatDuration(seconds) {
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = seconds % 60;
  if (h) return `${h}h ${m}m ${s}s`;
  if (m) return `${m}m ${s}s`;
  return `${s}s`;
}

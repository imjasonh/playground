// Tracks progress through a doc one word at a time.

/**
 * Reports whether a keydown should move to the next word. Only a fresh press
 * of Right Arrow or Space counts: a held key's auto-repeat doesn't, and
 * neither does a shortcut with a modifier.
 * @param {{key: string, repeat: boolean, altKey: boolean, ctrlKey: boolean,
 *     metaKey: boolean, shiftKey: boolean}} event
 * @return {boolean}
 */
export function isAdvanceKey(event) {
  if (event.repeat) return false;
  if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) {
    return false;
  }
  return event.key === 'ArrowRight' || event.key === ' ';
}

/** Steps through `total` words. The clock starts at the first step. */
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
    this.finishedAt_ = null;
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
   * Marks the current word read.
   * @return {boolean} Whether the reader moved.
   */
  advance() {
    if (this.done) return false;
    this.startedAt_ ??= this.now_();
    this.index_++;
    if (this.done) this.finishedAt_ = this.now_();
    return true;
  }

  /** @return {?number} When the last word was read, in ms since the epoch. */
  get finishedAt() {
    return this.finishedAt_;
  }

  /** @return {number} Whole seconds from the first step to the last. */
  get seconds() {
    if (this.startedAt_ === null) return 0;
    const end = this.finishedAt_ ?? this.now_();
    return Math.round((end - this.startedAt_) / 1000);
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

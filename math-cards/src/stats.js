/**
 * @fileoverview The player's progress: the selected mode, and each mode's
 * answer counts and streaks, kept in localStorage.
 */

import {DEFAULT_MODE, isMode} from './problems.js';

const MODE_KEY = 'math-cards:mode';
const STATS_PREFIX = 'math-cards:v1';

// Addition was the only mode before each mode had its own stats, which were
// saved under STATS_PREFIX alone.
const LEGACY_MODE = 'addition';

/** A celebration plays each time the streak reaches a multiple of this. */
export const CELEBRATE_EVERY = 10;

/**
 * @typedef {object} Stats
 * @property {number} answered Cards answered, right or wrong.
 * @property {number} correct Cards answered right.
 * @property {number} streak Right answers in a row, up to now.
 * @property {number} best Longest streak.
 */

/**
 * Returns the stats after one more answer, and whether that answer earns a
 * celebration.
 * @param {!Stats} stats
 * @param {boolean} correct
 * @return {{stats: !Stats, celebrate: boolean}}
 */
export function recordAnswer(stats, correct) {
  const streak = correct ? stats.streak + 1 : 0;
  return {
    stats: {
      answered: stats.answered + 1,
      correct: stats.correct + (correct ? 1 : 0),
      streak,
      best: Math.max(stats.best, streak),
    },
    celebrate: correct && streak % CELEBRATE_EVERY === 0,
  };
}

/**
 * Returns how many of the CELEBRATE_EVERY progress dots to fill. All of
 * them stay filled at a multiple, so the full row shows during the
 * celebration, and the row empties on the next right answer.
 * @param {number} streak
 * @return {number}
 */
export function filledDots(streak) {
  if (streak === 0) {
    return 0;
  }
  return streak % CELEBRATE_EVERY || CELEBRATE_EVERY;
}

/**
 * Reads a key, or null when storage is missing or refuses.
 * @param {?Storage} storage
 * @param {string} key
 * @return {?string}
 */
function read(storage, key) {
  try {
    return storage?.getItem(key) ?? null;
  } catch {
    return null;
  }
}

/**
 * Writes a key. When storage is missing, full, or blocked, the value lasts
 * only in memory.
 * @param {?Storage} storage
 * @param {string} key
 * @param {string} value
 */
function write(storage, key, value) {
  try {
    storage?.setItem(key, value);
  } catch {
    // Progress keeps counting in memory.
  }
}

/**
 * Parses saved stats. A missing or malformed value reads as zero, field by
 * field.
 * @param {?string} saved
 * @return {!Stats}
 */
function parseStats(saved) {
  const stats = {answered: 0, correct: 0, streak: 0, best: 0};
  let parsed;
  try {
    parsed = JSON.parse(saved ?? 'null');
  } catch {
    return stats;
  }
  if (parsed == null || typeof parsed !== 'object') {
    return stats;
  }
  for (const key of Object.keys(stats)) {
    const value = parsed[key];
    if (Number.isSafeInteger(value) && value >= 0) {
      stats[key] = value;
    }
  }
  return stats;
}

/**
 * The selected mode and each mode's stats. Reads each from storage once and
 * keeps it in memory, so modes stay apart even when storage refuses writes.
 */
export class Progress {
  /** @param {?Storage} storage */
  constructor(storage) {
    /** @private @const {?Storage} */
    this.storage_ = storage;
    /** @private @const {!Map<string, !Stats>} */
    this.statsByMode_ = new Map();
    const saved = read(storage, MODE_KEY);
    /** @private {string} */
    this.mode_ = isMode(saved) ? saved : DEFAULT_MODE;
  }

  /** @return {string} The selected mode. */
  get mode() {
    return this.mode_;
  }

  /** @return {!Stats} The selected mode's stats. */
  get stats() {
    const mode = this.mode_;
    if (!this.statsByMode_.has(mode)) {
      let saved = read(this.storage_, `${STATS_PREFIX}:${mode}`);
      if (saved == null && mode === LEGACY_MODE) {
        saved = read(this.storage_, STATS_PREFIX);
      }
      this.statsByMode_.set(mode, parseStats(saved));
    }
    return this.statsByMode_.get(mode);
  }

  /** @param {string} mode A key in MODES. */
  selectMode(mode) {
    if (!isMode(mode)) {
      throw new Error(`unknown mode ${mode}`);
    }
    this.mode_ = mode;
    write(this.storage_, MODE_KEY, mode);
  }

  /**
   * Records an answer in the selected mode.
   * @param {boolean} correct
   * @return {boolean} Whether the answer earns a celebration.
   */
  record(correct) {
    const {stats, celebrate} = recordAnswer(this.stats, correct);
    this.statsByMode_.set(this.mode_, stats);
    write(this.storage_, `${STATS_PREFIX}:${this.mode_}`,
        JSON.stringify(stats));
    return celebrate;
  }
}

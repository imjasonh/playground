/**
 * @fileoverview Answer counts and streaks for each mode, kept in
 * localStorage.
 */

const KEY_PREFIX = 'math-cards:v1';

/**
 * Addition was the only mode before modes had their own stats, so its
 * stats fall back to the key from then.
 */
export const LEGACY_KEY = KEY_PREFIX;
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

/** @return {!Stats} */
export function emptyStats() {
  return {answered: 0, correct: 0, streak: 0, best: 0};
}

/**
 * @param {string} mode
 * @return {string} The storage key for the mode's stats.
 */
export function statsKey(mode) {
  return `${KEY_PREFIX}:${mode}`;
}

/**
 * @param {?Storage} storage
 * @param {string} mode
 * @return {?string}
 */
function readSaved(storage, mode) {
  const saved = storage?.getItem(statsKey(mode)) ?? null;
  if (saved == null && mode === LEGACY_MODE) {
    return storage?.getItem(LEGACY_KEY) ?? null;
  }
  return saved;
}

/**
 * Reads a mode's stats from storage. A missing, unreadable, or malformed
 * value reads as zero, field by field.
 * @param {?Storage} storage
 * @param {string} mode
 * @return {!Stats}
 */
export function loadStats(storage, mode) {
  const stats = emptyStats();
  let saved;
  try {
    saved = JSON.parse(readSaved(storage, mode) ?? 'null');
  } catch {
    return stats;
  }
  if (saved == null || typeof saved !== 'object') {
    return stats;
  }
  for (const key of Object.keys(stats)) {
    const value = saved[key];
    if (Number.isSafeInteger(value) && value >= 0) {
      stats[key] = value;
    }
  }
  return stats;
}

/**
 * Writes a mode's stats to storage. Returns false when the browser
 * refuses, such as when storage is full or blocked, so the page keeps
 * counting in memory.
 * @param {?Storage} storage
 * @param {string} mode
 * @param {!Stats} stats
 * @return {boolean}
 */
export function saveStats(storage, mode, stats) {
  if (!storage) {
    return false;
  }
  try {
    storage.setItem(statsKey(mode), JSON.stringify(stats));
    return true;
  } catch {
    return false;
  }
}

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

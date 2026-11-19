/**
 * @fileoverview Answer counts and streaks, kept in localStorage.
 */

export const STORAGE_KEY = 'math-cards:v1';

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
 * Reads stats from storage. A missing, unreadable, or malformed value
 * reads as zero, field by field.
 * @param {?Storage} storage
 * @return {!Stats}
 */
export function loadStats(storage) {
  const stats = emptyStats();
  let saved;
  try {
    saved = JSON.parse(storage?.getItem(STORAGE_KEY) ?? 'null');
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
 * Writes stats to storage. Returns false when the browser refuses, such as
 * when storage is full or blocked, so the page keeps counting in memory.
 * @param {?Storage} storage
 * @param {!Stats} stats
 * @return {boolean}
 */
export function saveStats(storage, stats) {
  if (!storage) {
    return false;
  }
  try {
    storage.setItem(STORAGE_KEY, JSON.stringify(stats));
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

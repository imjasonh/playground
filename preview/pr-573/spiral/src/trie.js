/**
 * Segment uppercase dictionary words for spiral generation.
 */

/**
 * Every non-empty proper suffix of every dictionary word.
 * Used when a partial reverse fill starts mid-word.
 */
export function buildSuffixSet(words) {
  const suffixes = new Set();
  for (const word of words) {
    for (let i = 1; i < word.length; i += 1) {
      suffixes.add(word.slice(i));
    }
  }
  return suffixes;
}

/**
 * Segment `text` into dictionary words (O(n · maxLen) DP).
 * Returns the words, or null if impossible.
 *
 * @param {string} text
 * @param {Set<string>} wordSet
 * @param {number} [minLen]
 * @param {number} [maxLen]
 * @param {{ forbiddenWords?: Set<string> | null, forbiddenSeams?: Set<number> | null } | null} [opts]
 *   forbiddenSeams: cuts after cell N that outward must not use. When `text`
 *   is the reversed spiral, finishing a word after `j` reverse letters makes
 *   the forward seam after cell `text.length - j`.
 */
export function wordBreak(
  text,
  wordSet,
  minLen = 3,
  maxLen = 8,
  opts = null,
) {
  const forbiddenWords = opts?.forbiddenWords ?? null;
  const forbiddenSeams = opts?.forbiddenSeams ?? null;
  const n = text.length;

  function seamAllowed(endExclusive) {
    if (!forbiddenSeams || endExclusive >= n) return true;
    return !forbiddenSeams.has(n - endExclusive);
  }

  const prev = new Array(n + 1).fill(-1);
  const prevWord = new Array(n + 1).fill("");
  prev[0] = -2;
  for (let i = 0; i < n; i += 1) {
    if (prev[i] === -1) continue;
    const upper = Math.min(n, i + maxLen);
    for (let j = i + minLen; j <= upper; j += 1) {
      if (prev[j] !== -1) continue;
      const piece = text.slice(i, j);
      if (!wordSet.has(piece)) continue;
      if (forbiddenWords?.has(piece)) continue;
      if (!seamAllowed(j)) continue;
      prev[j] = i;
      prevWord[j] = piece;
    }
  }
  if (prev[n] === -1) return null;

  const words = [];
  for (let i = n; i > 0; i = prev[i]) {
    words.push(prevWord[i]);
  }
  words.reverse();
  return words;
}

/**
 * True when `rev` (reverse of letters filled from the outside) can finish as
 * the trailing end of some outward word-break: either a full break, or a
 * dictionary-word suffix followed by a full break.
 */
export function isValidOutwardSuffix(
  rev,
  wordSet,
  suffixSet,
  minLen = 3,
  maxLen = 8,
) {
  const n = rev.length;
  if (n === 0) return true;

  const canBreakFrom = new Array(n + 1).fill(false);
  canBreakFrom[n] = true;
  for (let i = n - 1; i >= 0; i -= 1) {
    const upper = Math.min(n, i + maxLen);
    for (let j = i + minLen; j <= upper; j += 1) {
      if (canBreakFrom[j] && wordSet.has(rev.slice(i, j))) {
        canBreakFrom[i] = true;
        break;
      }
    }
  }

  if (canBreakFrom[0]) return true;

  for (let i = 1; i <= Math.min(n, maxLen - 1); i += 1) {
    if (canBreakFrom[i] && suffixSet.has(rev.slice(0, i))) return true;
  }
  return false;
}

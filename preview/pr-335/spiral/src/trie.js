/**
 * Prefix trie over uppercase dictionary words.
 * Used for generation pruning and reverse-path word breaks.
 */
export function buildTrie(words) {
  const root = { kids: Object.create(null), end: false };
  for (const word of words) {
    let node = root;
    for (const ch of word) {
      if (!node.kids[ch]) {
        node.kids[ch] = { kids: Object.create(null), end: false };
      }
      node = node.kids[ch];
    }
    node.end = true;
  }
  return root;
}

/** True when `word` is in the trie. */
export function hasWord(trie, word) {
  let node = trie;
  for (const ch of word) {
    node = node.kids[ch];
    if (!node) return false;
  }
  return node.end;
}

/**
 * Build a set of every non-empty suffix of every dictionary word.
 * Used when the reverse path may start mid-word on a partial fill.
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
 * Segment `text` into dictionary words (greedy leftmost DP).
 * Returns an array of words, or null if impossible.
 *
 * When `forbiddenWords` is provided, those answers are skipped so a puzzle can
 * avoid repeating an inward answer on the outward path.
 */
export function wordBreak(
  text,
  wordSet,
  minLen = 3,
  maxLen = 8,
  forbiddenWords = null,
) {
  const n = text.length;
  const best = new Array(n + 1).fill(null);
  best[0] = [];
  for (let i = 0; i < n; i += 1) {
    if (!best[i]) continue;
    const upper = Math.min(n, i + maxLen);
    for (let j = i + minLen; j <= upper; j += 1) {
      if (best[j]) continue;
      const piece = text.slice(i, j);
      if (!wordSet.has(piece)) continue;
      if (forbiddenWords && forbiddenWords.has(piece)) continue;
      best[j] = best[i].concat(piece);
    }
  }
  return best[n];
}

/**
 * True when `rev` (the reverse of letters filled from the outside) can be the
 * trailing end of some full outward word-break.
 *
 * That means there is a cut index `i` where:
 * - rev.slice(0, i) is empty, a whole word, or a suffix of some dictionary word
 * - rev.slice(i) word-breaks into zero or more dictionary words
 */
export function isValidOutwardSuffix(rev, wordSet, suffixSet, minLen = 3, maxLen = 8) {
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
    if (!canBreakFrom[i]) continue;
    const head = rev.slice(0, i);
    if (suffixSet.has(head)) return true;
  }
  return false;
}

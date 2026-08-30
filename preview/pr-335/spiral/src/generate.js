import { ENTRIES, WORD_SET, clueFor, displayFor } from "./words.js";
import { buildSuffixSet, isValidOutwardSuffix, wordBreak } from "./trie.js";
import { mulberry32, shuffle } from "./rng.js";

const MIN_LEN = 3;
const MAX_LEN = 8;

/**
 * @typedef {{
 *   start: number,
 *   end: number,
 *   word: string,
 *   clue: string,
 *   display: string
 * }} ClueSpan
 *
 * @typedef {{
 *   size: number,
 *   letters: string,
 *   inward: ClueSpan[],
 *   outward: ClueSpan[],
 *   seed: number
 * }} Puzzle
 */

function groupByLength(entries) {
  /** @type {Record<number, string[]>} */
  const byLen = {};
  for (let len = MIN_LEN; len <= MAX_LEN; len += 1) byLen[len] = [];
  for (const entry of entries) {
    const len = entry.word.length;
    if (len >= MIN_LEN && len <= MAX_LEN) byLen[len].push(entry.word);
  }
  return byLen;
}

const BY_LEN = groupByLength(ENTRIES);
const SUFFIX_SET = buildSuffixSet([...WORD_SET]);

function reverseString(text) {
  return text.split("").reverse().join("");
}

function spansFromWords(words, fromStart) {
  /** @type {ClueSpan[]} */
  const spans = [];
  if (fromStart) {
    let pos = 1;
    for (const word of words) {
      const start = pos;
      const end = pos + word.length - 1;
      spans.push({
        start,
        end,
        word,
        clue: clueFor(word),
        display: displayFor(word),
      });
      pos = end + 1;
    }
  } else {
    let pos = words.reduce((n, w) => n + w.length, 0);
    for (const word of words) {
      const end = pos;
      const start = pos - word.length + 1;
      spans.push({
        start: end,
        end: start,
        word,
        clue: clueFor(word),
        display: displayFor(word),
      });
      pos = start - 1;
    }
  }
  return spans;
}

function cluesAreUnique(spans) {
  const seen = new Set();
  for (const span of spans) {
    if (seen.has(span.clue)) return false;
    seen.add(span.clue);
  }
  return true;
}

/**
 * Preferred lengths: favor 4–7 like magazine spirals; avoid leaving 1–2 cells.
 * @param {number} remaining
 * @param {() => number} rng
 */
function candidateLengths(remaining, rng) {
  if (remaining <= MAX_LEN && remaining >= MIN_LEN) {
    const preferred = [5, 6, 4, 7, 3, 8].filter((len) => len === remaining);
    const others = [5, 6, 4, 7, 3, 8].filter(
      (len) => len <= remaining && len !== remaining && remaining - len >= MIN_LEN,
    );
    return preferred.concat(shuffle(others, rng));
  }
  const lengths = [5, 6, 4, 7, 3, 8].filter(
    (len) => len <= remaining && remaining - len >= MIN_LEN,
  );
  return shuffle(lengths, rng);
}

/**
 * Generate a spiral puzzle of the given size.
 *
 * @param {{ size?: number, seed?: number, maxNodes?: number }} [options]
 * @returns {Puzzle | null}
 */
export function generatePuzzle(options = {}) {
  const size = options.size ?? 48;
  const seed = options.seed ?? (Math.floor(Math.random() * 0xffffffff) >>> 0);
  const maxNodes = options.maxNodes ?? size * 8000;
  const rng = mulberry32(seed);

  /** @type {string[]} */
  const letters = [];
  /** @type {string[]} */
  const inwardWords = [];
  /** @type {Set<string>} */
  const usedWords = new Set();
  let nodes = 0;

  function search() {
    nodes += 1;
    if (nodes > maxNodes) return false;

    if (letters.length === size) {
      const outwardWords = wordBreak(
        reverseString(letters.join("")),
        WORD_SET,
        MIN_LEN,
        MAX_LEN,
      );
      return Boolean(outwardWords);
    }

    const remaining = size - letters.length;
    for (const len of candidateLengths(remaining, rng)) {
      const pool = shuffle(BY_LEN[len], rng);
      const limit = Math.min(pool.length, len <= 4 ? 40 : 60);
      for (let i = 0; i < limit; i += 1) {
        const word = pool[i];
        if (usedWords.has(word)) continue;
        for (const ch of word) letters.push(ch);
        const rev = reverseString(letters.join(""));
        if (isValidOutwardSuffix(rev, WORD_SET, SUFFIX_SET, MIN_LEN, MAX_LEN)) {
          inwardWords.push(word);
          usedWords.add(word);
          if (search()) return true;
          usedWords.delete(word);
          inwardWords.pop();
        }
        letters.length -= len;
      }
    }
    return false;
  }

  if (!search()) return null;

  const text = letters.join("");
  // Prefer an outward break that shares no answers (hence no clues) with inward.
  const outwardWords =
    wordBreak(reverseString(text), WORD_SET, MIN_LEN, MAX_LEN, usedWords) ||
    wordBreak(reverseString(text), WORD_SET, MIN_LEN, MAX_LEN);
  if (!outwardWords) return null;

  const puzzle = {
    size,
    letters: text,
    inward: spansFromWords(inwardWords, true),
    outward: spansFromWords(outwardWords, false),
    seed,
  };
  if (!cluesAreUnique([...puzzle.inward, ...puzzle.outward])) return null;
  return puzzle;
}

/**
 * Validate that a puzzle's letters match both clue directions and that every
 * clue text appears at most once.
 * @param {Puzzle} puzzle
 */
export function validatePuzzle(puzzle) {
  const { letters, inward, outward, size } = puzzle;
  if (letters.length !== size) return false;
  if (!/^[A-Z]+$/.test(letters)) return false;
  if (!cluesAreUnique([...inward, ...outward])) return false;

  for (const span of inward) {
    const slice = letters.slice(span.start - 1, span.end);
    if (slice !== span.word) return false;
  }

  const reversed = reverseString(letters);
  let pos = 0;
  for (const span of outward) {
    const expectedLen = Math.abs(span.start - span.end) + 1;
    const slice = reversed.slice(pos, pos + expectedLen);
    if (slice !== span.word) return false;
    pos += expectedLen;
  }
  return pos === size;
}

/**
 * Retry generation with new seeds until one succeeds.
 * @param {{ size?: number, seed?: number, attempts?: number, maxNodes?: number }} [options]
 */
export function generatePuzzleWithRetry(options = {}) {
  const attempts = options.attempts ?? 24;
  let seed = options.seed ?? (Math.floor(Math.random() * 0xffffffff) >>> 0);
  for (let i = 0; i < attempts; i += 1) {
    const puzzle = generatePuzzle({
      size: options.size,
      seed: (seed + i * 0x9e3779b9) >>> 0,
      maxNodes: options.maxNodes,
    });
    if (puzzle && validatePuzzle(puzzle)) return puzzle;
  }
  return null;
}

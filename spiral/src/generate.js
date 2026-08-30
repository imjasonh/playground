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
 * Seams are cuts after cell N (between N and N+1), 1-based.
 * @param {number[]} lengths
 * @param {"inward" | "outward"} dir
 * @param {number} size
 */
export function seamsFromLengths(lengths, dir, size) {
  /** @type {Set<number>} */
  const seams = new Set();
  if (dir === "inward") {
    let cum = 0;
    for (let i = 0; i < lengths.length - 1; i += 1) {
      cum += lengths[i];
      seams.add(cum);
    }
  } else {
    let cum = 0;
    for (let i = 0; i < lengths.length - 1; i += 1) {
      cum += lengths[i];
      seams.add(size - cum);
    }
  }
  return seams;
}

function spanKey(span) {
  const lo = Math.min(span.start, span.end);
  const hi = Math.max(span.start, span.end);
  return `${lo}-${hi}`;
}

/**
 * Inward/outward must interlock: no shared seams, no identical cell ranges.
 * Shared seams are what stall solvers — a break in one direction must never
 * land on a break in the other.
 * @param {ClueSpan[]} inward
 * @param {ClueSpan[]} outward
 * @param {number} size
 */
export function partitionsInterlock(inward, outward, size) {
  if (inward.length < 2 || outward.length < 2) return false;

  const inSeams = seamsFromLengths(
    inward.map((s) => Math.abs(s.start - s.end) + 1),
    "inward",
    size,
  );
  const outSeams = seamsFromLengths(
    outward.map((s) => Math.abs(s.start - s.end) + 1),
    "outward",
    size,
  );

  for (const seam of inSeams) {
    if (outSeams.has(seam)) return false;
  }

  const outKeys = new Set(outward.map(spanKey));
  for (const span of inward) {
    if (outKeys.has(spanKey(span))) return false;
  }

  return true;
}

/**
 * Preferred lengths: favor 4–7 like magazine spirals; avoid leaving 1–2 cells.
 * @param {number} remaining
 * @param {() => number} rng
 * @param {number} _size
 */
function candidateLengths(remaining, rng, _size) {
  const order = [5, 6, 4, 7, 3, 8];
  if (remaining <= MAX_LEN && remaining >= MIN_LEN) {
    const preferred = order.filter((len) => len === remaining);
    const others = order.filter(
      (len) => len < remaining && remaining - len >= MIN_LEN,
    );
    return preferred.concat(shuffle(others, rng));
  }
  const lengths = order.filter(
    (len) => len <= remaining && remaining - len >= MIN_LEN,
  );
  return shuffle(lengths, rng);
}

/**
 * Re-segment the reverse path so outward seams avoid every inward seam.
 * If a break reuses an inward answer, forbid those answers and try again.
 * @param {string[]} inwardWords
 * @param {Set<string>} usedWords
 * @param {number} size
 * @param {string} letters
 */
function findInterlockedOutward(inwardWords, usedWords, size, letters) {
  const inwardSeams = seamsFromLengths(
    inwardWords.map((w) => w.length),
    "inward",
    size,
  );
  const rev = reverseString(letters);
  /** @type {Set<string>} */
  const forbidden = new Set();

  for (let round = 0; round < 16; round += 1) {
    const staggered = wordBreak(rev, WORD_SET, MIN_LEN, MAX_LEN, {
      forbiddenSeams: inwardSeams,
      forbiddenWords: forbidden.size > 0 ? forbidden : null,
    });
    if (!staggered) return null;

    let clean = true;
    const seen = new Set();
    for (const word of staggered) {
      if (usedWords.has(word) || seen.has(word)) {
        forbidden.add(word);
        clean = false;
      }
      seen.add(word);
    }
    if (!clean) continue;

    const inward = spansFromWords(inwardWords, true);
    const outward = spansFromWords(staggered, false);
    if (!partitionsInterlock(inward, outward, size)) return null;
    return staggered;
  }
  return null;
}

/**
 * Generate a spiral puzzle of the given size.
 *
 * Search finds a valid letter string quickly. Interlocking is enforced afterward
 * by re-breaking the reverse path so outward seams never land on inward seams.
 * Seeds that cannot stagger return null for `generatePuzzleWithRetry`.
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
      return Boolean(
        wordBreak(reverseString(letters.join("")), WORD_SET, MIN_LEN, MAX_LEN),
      );
    }

    const remaining = size - letters.length;
    for (const len of candidateLengths(remaining, rng, size)) {
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

  const outwardWords = findInterlockedOutward(
    inwardWords,
    usedWords,
    size,
    letters.join(""),
  );
  if (!outwardWords) return null;

  const puzzle = {
    size,
    letters: letters.join(""),
    inward: spansFromWords(inwardWords, true),
    outward: spansFromWords(outwardWords, false),
    seed,
  };
  if (!cluesAreUnique([...puzzle.inward, ...puzzle.outward])) return null;
  if (!partitionsInterlock(puzzle.inward, puzzle.outward, size)) return null;
  return puzzle;
}

/**
 * Validate letters, unique clues, and interlocking partitions.
 * @param {Puzzle} puzzle
 */
export function validatePuzzle(puzzle) {
  const { letters, inward, outward, size } = puzzle;
  if (letters.length !== size) return false;
  if (!/^[A-Z]+$/.test(letters)) return false;
  if (!cluesAreUnique([...inward, ...outward])) return false;
  if (!partitionsInterlock(inward, outward, size)) return false;

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
  const size = options.size ?? 48;
  const attempts = options.attempts ?? Math.max(120, size * 5);
  let seed = options.seed ?? (Math.floor(Math.random() * 0xffffffff) >>> 0);
  for (let i = 0; i < attempts; i += 1) {
    const puzzle = generatePuzzle({
      size,
      seed: (seed + i * 0x9e3779b9) >>> 0,
      maxNodes: options.maxNodes ?? size * 8000,
    });
    if (puzzle && validatePuzzle(puzzle)) return puzzle;
  }
  return null;
}

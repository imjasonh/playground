/**
 * Turns a slide's speaker notes into cues: short runs of text that are spoken
 * one at a time and shown as one subtitle each.
 *
 * Speaking a cue at a time keeps each utterance short. Chrome's network voices
 * stop after about 15 seconds of one utterance and never fire `end`, which is
 * what stalled the original marptalk on long notes.
 */

/** Longest cue, in characters: about two subtitle lines. */
export const MAX_CUE_CHARS = 120;

/** Speaking pace at rate 1, in words per minute. */
export const WORDS_PER_MINUTE = 165;

/**
 * Strips Markdown that a voice would read aloud or a subtitle would show
 * literally, and collapses whitespace.
 *
 * @param {string} note
 * @return {string}
 */
export function toSpokenText(note) {
  return note
    .replace(/```[\s\S]*?```/g, ' ')
    .replace(/!\[[^\]]*\]\([^)]*\)/g, ' ')
    .replace(/\[([^\]]+)\]\([^)]*\)/g, '$1')
    .replace(/`([^`]+)`/g, '$1')
    .replace(/(\*\*|__)(.+?)\1/g, '$2')
    .replace(/(^|[\s(])[*_]([^*_\s][^*_]*?)[*_](?=[\s).,;:!?]|$)/g, '$1$2')
    .replace(/^\s*(?:[-*+]|\d+\.|#{1,6})\s+/gm, '')
    .replace(/\s+/g, ' ')
    .trim();
}

/**
 * Splits text into sentences.
 *
 * @param {string} text
 * @param {string=} lang BCP 47 language tag for sentence rules.
 * @return {!Array<string>}
 */
export function splitSentences(text, lang = 'en') {
  if (!text) return [];
  let parts;
  if (typeof Intl !== 'undefined' && Intl.Segmenter) {
    let segmenter;
    try {
      segmenter = new Intl.Segmenter(lang, {granularity: 'sentence'});
    } catch {
      segmenter = new Intl.Segmenter('en', {granularity: 'sentence'});
    }
    parts = Array.from(segmenter.segment(text), (s) => s.segment.trim());
  } else {
    parts = (text.match(/[^.!?]+(?:[.!?]+["')\]]*|$)/g) || []).map((s) =>
      s.trim(),
    );
  }
  const sentences = [];
  for (const part of parts.filter(Boolean)) {
    const prev = sentences.at(-1);
    if (prev && ABBREVIATION.test(prev)) {
      sentences[sentences.length - 1] = `${prev} ${part}`;
    } else {
      sentences.push(part);
    }
  }
  return sentences;
}

/** Titles and initials that end in a period but don't end a sentence. */
const ABBREVIATION =
  /(?:^|\s)(?:Mr|Mrs|Ms|Dr|Prof|Sr|Jr|St|Mt|vs|[A-Z]|(?:[A-Z]\.)+[A-Z])\.$/;

/** Shortest piece a clause break may leave, so cues aren't one word. */
const MIN_PIECE = 24;

/**
 * Finds the match of `re` closest to the middle of `text` that leaves at least
 * `min` characters on each side.
 *
 * @param {string} text
 * @param {!RegExp} re A global regular expression.
 * @param {number} min
 * @return {?number} The index after the match, or null.
 */
function nearestCut(text, re, min) {
  const mid = text.length / 2;
  let best = null;
  for (const m of text.matchAll(re)) {
    const cut = m.index + m[0].length;
    if (m.index < min || text.length - cut < min) continue;
    if (best === null || Math.abs(cut - mid) < Math.abs(best - mid)) {
      best = cut;
    }
  }
  return best;
}

/**
 * Splits one sentence into pieces of at most `max` characters, preferring
 * clause punctuation, then the space nearest the middle.
 *
 * @param {string} sentence
 * @param {number} max
 * @return {!Array<string>}
 */
function splitLong(sentence, max) {
  if (sentence.length <= max) return [sentence];
  const best =
    nearestCut(sentence, /[,;:\u2013\u2014]\s+/g, MIN_PIECE) ??
    nearestCut(sentence, /\s+/g, 1);
  if (best === null) return [sentence];
  return [
    ...splitLong(sentence.slice(0, best).trim(), max),
    ...splitLong(sentence.slice(best).trim(), max),
  ];
}

/**
 * Turns raw speaker notes into cues.
 *
 * @param {string} note
 * @param {{lang?: string, max?: number}=} options
 * @return {!Array<string>}
 */
export function toCues(note, {lang = 'en', max = MAX_CUE_CHARS} = {}) {
  return splitSentences(toSpokenText(note), lang).flatMap((s) =>
    splitLong(s, max),
  );
}

/**
 * Counts words, treating each CJK character as a word.
 *
 * @param {string} text
 * @return {number}
 */
export function countWords(text) {
  const cjk = text.match(/[\u3040-\u30ff\u3400-\u9fff\uac00-\ud7af]/g);
  const rest = text
    .replace(/[\u3040-\u30ff\u3400-\u9fff\uac00-\ud7af]/g, ' ')
    .split(/\s+/)
    .filter(Boolean);
  return rest.length + (cjk ? cjk.length / 2 : 0);
}

/**
 * Estimates how long a voice takes to say `text` at `rate`.
 *
 * @param {string} text
 * @param {number=} rate
 * @return {number} Milliseconds.
 */
export function estimateMs(text, rate = 1) {
  const words = countWords(text);
  if (!words) return 0;
  const pauses = (text.match(/[,;:.!?]/g) || []).length * 120;
  return ((words / WORDS_PER_MINUTE) * 60000 + pauses + 250) / rate;
}

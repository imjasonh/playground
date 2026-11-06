/**
 * Finds problems in a marptalk deck that make it worse to watch or listen to.
 * `scripts/check.js` runs these checks from the command line.
 */
import {parseDeck} from './deck.js';
import {countWords, toSpokenText} from './script.js';

/** Most words of narration on one slide: about a minute at rate 1. */
export const MAX_NOTE_WORDS = 160;

/** Most words of visible text on one slide. */
export const MAX_SLIDE_WORDS = 50;

/**
 * A problem on one slide. `slide` is 1-based, or 0 for the whole deck.
 *
 * @typedef {{slide: number, message: string}} Finding
 */

/**
 * Splits Marp's HTML into the inner HTML of each slide.
 *
 * @param {string} html
 * @return {!Array<string>}
 */
function slideBodies(html) {
  const sections =
    /<section\b((?:[^>"']|"[^"]*"|'[^']*')*)>([\s\S]*?)<\/section>/g;
  return Array.from(html.matchAll(sections))
    .filter(([, attrs]) => /\sid="\d+"/.test(attrs))
    .map(([, , body]) => body);
}

/**
 * @param {string} body
 * @return {string} The slide's visible text, without code blocks.
 */
function visibleText(body) {
  return body
    .replace(/<pre[\s\S]*?<\/pre>/g, ' ')
    .replace(/<[^>]+>/g, ' ')
    .replace(/&[a-z#0-9]+;/gi, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

/**
 * Lists tags that the HTML allowlist escaped, so they show as text.
 *
 * @param {string} body
 * @return {!Array<string>}
 */
function escapedTags(body) {
  const outsideCode = body
    .replace(/<pre[\s\S]*?<\/pre>/g, ' ')
    .replace(/<code[\s\S]*?<\/code>/g, ' ');
  const tags = Array.from(
    outsideCode.matchAll(/&lt;([a-zA-Z][\w-]*)/g),
    (m) => m[1],
  );
  return [...new Set(tags)];
}

/**
 * @param {string} markdown
 * @return {!Array<!Finding>}
 */
export function lintDeck(markdown) {
  /** @type {!Array<!Finding>} */
  const findings = [];
  const add = (slide, message) => findings.push({slide, message});

  if (!/^\uFEFF?---\r?\n[\s\S]*?^marp:\s*true\s*$/m.test(markdown)) {
    add(0, 'Front matter should set `marp: true`.');
  }
  if (/(^|[^\\$])\$\$?[^\s$][^$\n]*\$/m.test(markdown)) {
    add(0, 'Math ($...$) is not rendered. Write the formula as text or code.');
  }
  for (const [svg] of markdown.matchAll(/<svg\b[\s\S]*?<\/svg>/g)) {
    if (/\n[ \t]*\r?\n/.test(svg)) {
      add(0, 'An <svg> has a blank line, which ends it early. Remove it.');
      break;
    }
  }

  const deck = parseDeck(markdown);
  if (!deck.slides.length) add(0, 'The deck has no slides.');
  const bodies = slideBodies(deck.html);

  deck.slides.forEach((slide, i) => {
    const n = i + 1;
    const body = bodies[i] ?? '';
    const shown = countWords(visibleText(body));
    if (shown > MAX_SLIDE_WORDS) {
      add(n, `Slide shows ${shown} words. Move detail into the voiceover.`);
    }
    for (const tag of escapedTags(body)) {
      add(n, `<${tag}> is not allowed, so it shows as text.`);
    }

    const notes = slide.notes;
    if (!notes) {
      add(n, 'No voiceover. Add a <!-- comment --> with the narration.');
      return;
    }
    const plain = notes.replace(/\s+/g, ' ').trim();
    if (toSpokenText(notes) !== plain) {
      add(n, 'Voiceover has Markdown. Write it as plain spoken sentences.');
    }
    if (/https?:\/\/|www\./.test(notes)) {
      add(n, 'Voiceover has a URL. Say where to find it instead.');
    }
    if (/->|=>|<-|\p{Extended_Pictographic}/u.test(notes)) {
      add(n, 'Voiceover has arrows or emoji. Say them in words.');
    }
    const words = countWords(slide.cues.join(' '));
    if (words > MAX_NOTE_WORDS) {
      add(n, `Voiceover is ${words} words. Split the slide; aim for 40-120.`);
    }
  });
  return findings;
}

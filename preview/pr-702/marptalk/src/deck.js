/**
 * Renders a Marp Markdown deck with Marp Core and pairs each slide with the
 * voiceover in its speaker notes.
 */
import {Marp} from '../vendor/marp.js';

import {estimateMs, toCues} from './script.js';

/**
 * @typedef {{notes: string, cues: !Array<string>}} Slide
 */

/**
 * @typedef {{
 *   title: string,
 *   lang: string,
 *   html: string,
 *   css: string,
 *   slides: !Array<!Slide>,
 * }} Deck
 */

const SVG_ATTRS = [
  'class',
  'role',
  'aria-label',
  'transform',
  'fill',
  'fill-opacity',
  'stroke',
  'stroke-width',
  'stroke-opacity',
  'stroke-dasharray',
  'stroke-linecap',
  'stroke-linejoin',
  'opacity',
  'font-size',
  'font-weight',
  'font-family',
  'font-style',
  'text-anchor',
  'dominant-baseline',
];

/** Extra attributes per SVG element, on top of SVG_ATTRS. */
const SVG_ELEMENTS = {
  svg: ['viewBox', 'width', 'height', 'xmlns', 'preserveAspectRatio'],
  g: [],
  title: [],
  rect: ['x', 'y', 'width', 'height', 'rx', 'ry'],
  circle: ['cx', 'cy', 'r'],
  ellipse: ['cx', 'cy', 'rx', 'ry'],
  line: ['x1', 'y1', 'x2', 'y2'],
  polyline: ['points'],
  polygon: ['points'],
  path: ['d'],
  text: ['x', 'y', 'dx', 'dy'],
  tspan: ['x', 'y', 'dx', 'dy'],
};

/**
 * Marp's default HTML allowlist plus inline SVG drawing elements, so a deck
 * can carry its diagrams in one file. Scripts, event handlers, `style`, `id`,
 * `<foreignObject>`, and `<image>` stay out.
 */
const HTML_ALLOWLIST = {
  ...Marp.html,
  ...Object.fromEntries(
    Object.entries(SVG_ELEMENTS).map(([tag, attrs]) => [
      tag,
      [...SVG_ATTRS, ...attrs],
    ]),
  ),
};

/**
 * Reads a scalar from the front matter. Marp ignores keys it doesn't know,
 * such as `title`, so they aren't in `lastGlobalDirectives`.
 *
 * @param {string} markdown
 * @param {string} key
 * @return {string}
 */
function frontMatter(markdown, key) {
  const m = markdown.match(/^\uFEFF?---\r?\n([\s\S]*?)\r?\n---\s*(?:\r?\n|$)/);
  if (!m) return '';
  const line = m[1].match(new RegExp(`^${key}:\\s*(.+?)\\s*$`, 'm'));
  return line ? line[1].replace(/^(['"])(.*)\1$/, '$2') : '';
}

/**
 * @param {string} markdown
 * @return {string}
 */
function firstHeading(markdown) {
  const body = markdown.replace(/^\uFEFF?---\r?\n[\s\S]*?\r?\n---\s*\r?\n/, '');
  const m = body.match(/^#{1,6}\s+(.+?)\s*#*\s*$/m);
  return m ? m[1].replace(/[*_`]/g, '') : '';
}

/**
 * @param {string} markdown Marp Markdown.
 * @return {!Deck}
 */
export function parseDeck(markdown) {
  const marp = new Marp({
    math: false,
    script: false,
    html: HTML_ALLOWLIST,
  });
  const {html, css, comments} = marp.render(markdown);
  const lang = marp.lastGlobalDirectives.lang || 'en-US';
  const slides = comments.map((parts) => {
    const notes = parts.join('\n\n').trim();
    return {notes, cues: toCues(notes, {lang})};
  });
  return {
    title: frontMatter(markdown, 'title') || firstHeading(markdown) || 'Deck',
    lang,
    html,
    css,
    slides,
  };
}

/**
 * Estimates how long the deck takes to narrate at `rate`.
 *
 * @param {!Deck} deck
 * @param {number=} rate
 * @return {number} Milliseconds.
 */
export function deckDurationMs(deck, rate = 1) {
  return deck.slides.reduce(
    (sum, s) => sum + estimateMs(s.cues.join(' '), rate),
    0,
  );
}

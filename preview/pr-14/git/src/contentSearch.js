/**
 * Pure content-search (grep) primitives: compile a query into a RegExp and scan
 * text for matching lines. Kept dependency-free and DOM-free so it runs
 * unchanged on the main thread (the fallback) and inside a worker, and is
 * unit-testable in isolation — the same hand-rolled, pure-function style as
 * fuzzy.js / diff.js.
 *
 * @typedef {Object} LineMatch
 * @property {number} line               1-based line number
 * @property {number} column             1-based column of the first match
 * @property {string} text               the (possibly clamped) line text
 * @property {[number, number][]} ranges [start, end) match spans within `text`
 */

/** Escape a string so it matches literally inside a RegExp. */
export function escapeRegExp(string) {
  return String(string).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/**
 * Compile a search query into a global RegExp.
 *
 * Plain queries are escaped (literal substring search); `regex: true` uses the
 * query verbatim. Case-insensitive by default. A bad regex returns its message
 * rather than throwing, so callers can show it inline. An empty query compiles
 * to `null` (nothing to search), not an error.
 *
 * @param {string} query
 * @param {{regex?: boolean, caseSensitive?: boolean}} [opts]
 * @returns {{re: RegExp|null, error: string|null}}
 */
export function buildPattern(query, opts = {}) {
  const q = query || '';
  if (q === '') return { re: null, error: null };
  const flags = opts.caseSensitive ? 'g' : 'gi';
  const source = opts.regex ? q : escapeRegExp(q);
  try {
    return { re: new RegExp(source, flags), error: null };
  } catch (err) {
    return { re: null, error: err.message };
  }
}

/** Truncate an over-long line and drop/clamp match ranges past the cut. */
function clampLine(line, ranges, maxLineLength) {
  if (line.length <= maxLineLength) return { text: line, ranges };
  const text = line.slice(0, maxLineLength);
  const clamped = [];
  for (const [start, end] of ranges) {
    if (start >= maxLineLength) break; // ranges are in order; the rest are past the cut
    clamped.push([start, Math.min(end, maxLineLength)]);
  }
  return { text, ranges: clamped };
}

/**
 * Scan `text` for lines matching `re`, returning one entry per matching line
 * (with every match span on that line) so the UI can show grep-style results.
 *
 * Bounds keep a single huge/minified file from producing unbounded work or DOM:
 * at most `maxMatches` lines, `maxPerLine` spans per line, and `maxLineLength`
 * characters of preview per line.
 *
 * @param {string} text
 * @param {RegExp} re                 a global RegExp (from {@link buildPattern})
 * @param {{maxMatches?: number, maxPerLine?: number, maxLineLength?: number}} [opts]
 * @returns {LineMatch[]}
 */
export function searchContent(text, re, opts = {}) {
  if (!re || !text) return [];
  const maxMatches = opts.maxMatches ?? 200;
  const maxPerLine = opts.maxPerLine ?? 50;
  const maxLineLength = opts.maxLineLength ?? 500;

  const results = [];
  const lines = text.split('\n');
  for (let i = 0; i < lines.length && results.length < maxMatches; i += 1) {
    const line = lines[i];
    re.lastIndex = 0;
    const ranges = [];
    let m;
    while ((m = re.exec(line)) !== null) {
      ranges.push([m.index, m.index + m[0].length]);
      // A zero-width match (e.g. the regex `a*`) wouldn't advance lastIndex;
      // nudge it so the scan terminates.
      if (m.index === re.lastIndex) re.lastIndex += 1;
      if (ranges.length >= maxPerLine) break;
    }
    if (ranges.length) {
      const clamped = clampLine(line, ranges, maxLineLength);
      results.push({
        line: i + 1,
        column: ranges[0][0] + 1,
        text: clamped.text,
        ranges: clamped.ranges,
      });
    }
  }
  return results;
}

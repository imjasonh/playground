/**
 * Minimal line-level diff for the diff view. Pure and dependency-free so it can
 * run anywhere (and, later, inside a worker) and be unit-tested in isolation.
 *
 * The algorithm is a classic longest-common-subsequence backtrace over lines —
 * not the most compact possible diff, but correct and easy to reason about. A
 * size guard keeps the O(n·m) table from blowing up on very large files (the
 * viewer already guards huge files; this is a second backstop).
 *
 * @typedef {Object} DiffRow
 * @property {'context'|'add'|'del'} type
 * @property {string} text
 * @property {number|null} oldLine  1-based line number on the old side, or null
 * @property {number|null} newLine  1-based line number on the new side, or null
 *
 * @typedef {Object} DiffResult
 * @property {DiffRow[]} rows
 * @property {number} added    count of added lines
 * @property {number} removed  count of removed lines
 * @property {boolean} truncated  true when the inputs were too large to diff
 */

/** Split text into lines, dropping a single trailing newline's empty line. */
export function splitLines(text) {
  if (text === '') return [];
  const lines = String(text).split('\n');
  if (lines.length > 1 && lines[lines.length - 1] === '' && text.endsWith('\n')) {
    lines.pop();
  }
  return lines;
}

// Cap the LCS table at ~4M cells (~16 MB as Uint32) so a pathological pair of
// large files degrades to a "too large" notice instead of locking the tab.
const MAX_CELLS = 4_000_000;

/**
 * @param {string} oldText
 * @param {string} newText
 * @param {{maxCells?: number}} [opts]
 * @returns {DiffResult}
 */
export function diffLines(oldText, newText, { maxCells = MAX_CELLS } = {}) {
  const a = splitLines(oldText);
  const b = splitLines(newText);
  const n = a.length;
  const m = b.length;

  if ((n + 1) * (m + 1) > maxCells) {
    return { rows: [], added: 0, removed: 0, truncated: true };
  }

  // lcs[i][j] = length of the LCS of a[i..] and b[j..].
  const lcs = Array.from({ length: n + 1 }, () => new Uint32Array(m + 1));
  for (let i = n - 1; i >= 0; i -= 1) {
    const row = lcs[i];
    const next = lcs[i + 1];
    for (let j = m - 1; j >= 0; j -= 1) {
      row[j] = a[i] === b[j] ? next[j + 1] + 1 : Math.max(next[j], row[j + 1]);
    }
  }

  const rows = [];
  let added = 0;
  let removed = 0;
  let i = 0;
  let j = 0;
  let oldLine = 1;
  let newLine = 1;

  while (i < n && j < m) {
    if (a[i] === b[j]) {
      rows.push({ type: 'context', text: a[i], oldLine: oldLine++, newLine: newLine++ });
      i += 1;
      j += 1;
    } else if (lcs[i + 1][j] >= lcs[i][j + 1]) {
      rows.push({ type: 'del', text: a[i], oldLine: oldLine++, newLine: null });
      removed += 1;
      i += 1;
    } else {
      rows.push({ type: 'add', text: b[j], oldLine: null, newLine: newLine++ });
      added += 1;
      j += 1;
    }
  }
  while (i < n) {
    rows.push({ type: 'del', text: a[i], oldLine: oldLine++, newLine: null });
    removed += 1;
    i += 1;
  }
  while (j < m) {
    rows.push({ type: 'add', text: b[j], oldLine: null, newLine: newLine++ });
    added += 1;
    j += 1;
  }

  return { rows, added, removed, truncated: false };
}

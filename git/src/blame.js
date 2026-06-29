/**
 * Pure "blame": attribute each line of a file's newest version to the commit
 * that last changed it, given the file's content at each commit in its history.
 *
 * The method is the standard incremental one — walk consecutive versions from
 * newest to oldest, diffing each pair:
 *   - a line present in the newer version but not its predecessor was last
 *     changed by the newer commit, and
 *   - a line common to both is carried back to keep looking for where it came
 *     from.
 * Whatever survives all the way to the oldest version we have is attributed to
 * that oldest commit (the earliest point our history can see).
 *
 * It builds only on the line diff in diff.js, so it's dependency-free, runs
 * anywhere (it could move into a worker later), and unit-tests in isolation.
 *
 * @typedef {Object} BlameVersion
 * @property {Object} commit   the commit that produced this version
 * @property {string|Uint8Array} content  the file's content at that commit
 *
 * @typedef {Object} BlameRow
 * @property {string} line    the line's text (no trailing newline)
 * @property {Object} commit  the commit that last changed it
 */
import { diffLines, splitLines } from './diff.js';

const decoder = new TextDecoder('utf-8', { fatal: false });

/** Coerce content (raw bytes or a string) to text for line diffing. */
function toText(content) {
  if (content == null) return '';
  if (typeof content === 'string') return content;
  if (content instanceof Uint8Array || ArrayBuffer.isView(content)) {
    return decoder.decode(content);
  }
  return String(content);
}

/**
 * Compute per-line blame for the newest version in `versions`.
 *
 * @param {BlameVersion[]} versions  newest first; each `content` is the file at
 *   that commit and each `commit` is passed through untouched onto the rows it
 *   accounts for. Versions without a `commit` are ignored.
 * @returns {BlameRow[]}  one row per line of the newest version (empty when
 *   there are no versions or the newest version is empty)
 */
export function blameLines(versions) {
  const list = (Array.isArray(versions) ? versions : []).filter((v) => v && v.commit);
  if (!list.length) return [];

  const lines = splitLines(toText(list[0].content));
  const n = lines.length;
  if (!n) return [];

  // blame[i] = commit for newest-version line i (null until attributed).
  const blame = new Array(n).fill(null);
  // origin[p] = the newest-version line index of the line now at position p in
  // the version under consideration. Starts as identity over the newest version
  // and is rebased onto each older version as we walk back.
  let origin = lines.map((_, i) => i);

  for (let v = 0; v < list.length - 1 && origin.length; v += 1) {
    const newerCommit = list[v].commit;
    const { rows, truncated } = diffLines(toText(list[v + 1].content), toText(list[v].content));
    // We declined to diff this (pathologically large) pair, so we can't refine
    // further; stop and let the tail attribute everything still tracked to the
    // oldest commit.
    if (truncated) break;

    const nextOrigin = [];
    for (const row of rows) {
      if (row.type === 'add') {
        // In the newer version, absent from the older one → newer changed it.
        // First writer wins (we go newest→oldest), so don't overwrite.
        const orig = origin[row.newLine - 1];
        if (orig != null && blame[orig] == null) blame[orig] = newerCommit;
      } else if (row.type === 'context') {
        // Survives into the older version; keep tracking it at its old position.
        nextOrigin[row.oldLine - 1] = origin[row.newLine - 1];
      }
      // 'del' rows live only in the older version: irrelevant to newest lines.
    }
    origin = nextOrigin;
  }

  // Anything that reached the oldest version we have was introduced there as far
  // as our history can see; attribute it — and, defensively, any straggler — to
  // that oldest commit.
  const oldest = list[list.length - 1].commit;
  for (let i = 0; i < n; i += 1) {
    if (blame[i] == null) blame[i] = oldest;
  }

  return lines.map((line, i) => ({ line, commit: blame[i] }));
}

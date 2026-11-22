/**
 * Helpers for git tree entries this read-only browser can't render as an
 * ordinary file, so the viewer can show a clear notice instead of garbage:
 *
 *   - symlinks   — a blob whose content is the link target path, and
 *   - submodules — a gitlink pinning another repository at a commit; the
 *                  referenced objects don't live in this clone at all.
 *
 * Everything here is pure (no git engine, no DOM) so it unit-tests directly.
 */

// Git stores a file's type in the high bits of its tree-entry mode. isomorphic-
// git surfaces that mode as a number from `walk()` (e.g. 33188) and as an octal
// string from `readTree()` (e.g. '100644'); `classifyGitMode` accepts either.
export const GIT_MODE = {
  TREE: 0o40000, // 16384  directory
  BLOB: 0o100644, // 33188  regular file
  EXECUTABLE: 0o100755, // 33261  executable file
  SYMLINK: 0o120000, // 40960  symbolic link
  SUBMODULE: 0o160000, // 57344  gitlink (commit)
};

/**
 * Map a git tree-entry mode to a coarse kind.
 *
 * @param {number|string} mode
 * @returns {'tree'|'symlink'|'submodule'|'executable'|'file'}
 */
export function classifyGitMode(mode) {
  const n = typeof mode === 'string' ? parseInt(mode, 8) : Number(mode);
  if (!Number.isFinite(n)) return 'file';
  switch (n) {
    case GIT_MODE.TREE:
      return 'tree';
    case GIT_MODE.SYMLINK:
      return 'symlink';
    case GIT_MODE.SUBMODULE:
      return 'submodule';
    case GIT_MODE.EXECUTABLE:
      return 'executable';
    default:
      return 'file';
  }
}

const decoder = new TextDecoder('utf-8', { fatal: false });

/**
 * The path a symlink points at: the blob's entire content (git stores it with
 * no trailing newline). We tolerate stray trailing newlines defensively but
 * keep interior characters intact, since link targets may contain spaces.
 *
 * @param {Uint8Array|string} input
 * @returns {string}
 */
export function symlinkTarget(input) {
  if (input == null) return '';
  const text = typeof input === 'string' ? input : decoder.decode(input);
  return text.replace(/\r?\n+$/, '');
}

/**
 * Parse a `.gitmodules` file (a git-config "INI" subset) into submodule info
 * keyed by the submodule's working-tree path, which is how the tree exposes the
 * corresponding gitlink.
 *
 * @param {Uint8Array|string} input
 * @returns {Map<string, {name: string, path: string, url: string, branch?: string}>}
 */
export function parseGitmodules(input) {
  const text =
    input == null ? '' : typeof input === 'string' ? input : decoder.decode(input);
  const byPath = new Map();
  let current = null;
  for (const rawLine of text.split('\n')) {
    const line = rawLine.trim();
    if (!line || line.startsWith('#') || line.startsWith(';')) continue;

    const header = line.match(/^\[submodule\s+"?(.*?)"?\]$/i);
    if (header) {
      current = { name: header[1], path: '', url: '' };
      continue;
    }
    // Any other section ends the current submodule block.
    if (line.startsWith('[')) {
      current = null;
      continue;
    }
    if (!current) continue;

    const eq = line.indexOf('=');
    if (eq === -1) continue;
    const key = line.slice(0, eq).trim().toLowerCase();
    const value = line.slice(eq + 1).trim();
    if (key === 'path') {
      current.path = value;
      // Same object reference, so a later url=/branch= still updates the map.
      if (value) byPath.set(value, current);
    } else if (key === 'url') {
      current.url = value;
    } else if (key === 'branch') {
      current.branch = value;
    }
  }
  return byPath;
}

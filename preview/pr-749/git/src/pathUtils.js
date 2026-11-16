/**
 * POSIX-style path helpers for repo file paths. Repo paths never use a leading
 * slash; they are always relative to the repository root (e.g. "src/app.js").
 */

/** Collapse duplicate slashes and strip leading "./" and surrounding slashes. */
export function normalizePath(path) {
  if (!path) return '';
  return String(path)
    .replace(/\\/g, '/')
    .replace(/^\.\//, '')
    .replace(/\/+/g, '/')
    .replace(/^\/+/, '')
    .replace(/\/+$/, '');
}

/** Split a path into its non-empty segments. */
export function splitPath(path) {
  const normalized = normalizePath(path);
  return normalized ? normalized.split('/') : [];
}

/** Last path segment (file or directory name). */
export function basename(path) {
  const segments = splitPath(path);
  return segments.length ? segments[segments.length - 1] : '';
}

/** Parent directory path, or '' when the path is at the repo root. */
export function dirname(path) {
  const segments = splitPath(path);
  segments.pop();
  return segments.join('/');
}

/**
 * File extension including the leading dot, lower-cased. Matches Node's
 * `path.extname` semantics for dotfiles: extname('.gitignore') === ''.
 */
export function extname(path) {
  const name = basename(path);
  const dot = name.lastIndexOf('.');
  if (dot <= 0) return '';
  return name.slice(dot).toLowerCase();
}

/** Join path parts, normalizing the result. */
export function joinPath(...parts) {
  return normalizePath(parts.filter(Boolean).join('/'));
}

/**
 * Resolve a symlink's target to a repo-root-relative path, applying POSIX
 * symlink semantics: the target is interpreted relative to the directory that
 * *contains* the link, with `.`/`..` collapsed.
 *
 * Returns null when the target can't be a path inside this repository — it's
 * empty, absolute (starts with '/', so it points outside the tree), or it walks
 * above the repo root with `..`. Callers treat null as "not a navigable link".
 *
 * @param {string} linkPath  the symlink's own path (e.g. 'a/b/link')
 * @param {string} target    the link target (e.g. '../c/file.txt')
 * @returns {string|null}    resolved repo path (e.g. 'a/c/file.txt'), or null
 */
export function resolveSymlinkTarget(linkPath, target) {
  if (target == null) return null;
  const raw = String(target).replace(/\\/g, '/').trim();
  if (raw === '' || raw.startsWith('/')) return null;

  const stack = splitPath(dirname(linkPath));
  for (const segment of raw.split('/')) {
    if (segment === '' || segment === '.') continue;
    if (segment === '..') {
      if (stack.length === 0) return null; // escapes the repository root
      stack.pop();
    } else {
      stack.push(segment);
    }
  }
  return stack.length ? stack.join('/') : null;
}

/**
 * Every ancestor directory path of a file, root-first.
 * ancestors('a/b/c.txt') -> ['a', 'a/b']
 */
export function ancestors(path) {
  const segments = splitPath(dirname(path));
  const out = [];
  let current = '';
  for (const segment of segments) {
    current = current ? `${current}/${segment}` : segment;
    out.push(current);
  }
  return out;
}

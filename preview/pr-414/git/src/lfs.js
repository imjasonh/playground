/**
 * Detect Git LFS pointer files.
 *
 * A file tracked by Git LFS isn't stored in the repository as its real bytes —
 * the committed blob is a tiny text "pointer" describing the object that lives
 * on a separate LFS server:
 *
 *   version https://git-lfs.github.com/spec/v1
 *   oid sha256:4d7a21...e2393
 *   size 12345
 *
 * This client never contacts an LFS server, so without detection we'd render
 * that pointer as if it were the file's contents (e.g. show three lines of
 * metadata for what is actually a 40 MB video). Detecting it lets the viewer
 * show a clear "stored with Git LFS" notice instead.
 *
 * Pure and dependency-free so it can be unit-tested without a DOM.
 *
 * @typedef {Object} LfsPointer
 * @property {string} version  the spec URL from the `version` line
 * @property {string} oid      the object id, e.g. "sha256:4d7a21…"
 * @property {number} size     the real object size in bytes
 */

// Real pointers are a handful of short lines; anything larger is the actual
// file. Capping the candidate size keeps us from decoding/scanning big blobs.
const MAX_POINTER_BYTES = 1024;
const SPEC_PREFIX = 'https://git-lfs.github.com/spec/';

const decoder = new TextDecoder('utf-8', { fatal: false });

/** Coerce bytes or a string into the candidate pointer text, or null if too big. */
function pointerText(input) {
  if (typeof input === 'string') {
    return input.length <= MAX_POINTER_BYTES ? input : null;
  }
  if (input && typeof input.length === 'number') {
    if (input.length === 0 || input.length > MAX_POINTER_BYTES) return null;
    return decoder.decode(input);
  }
  return null;
}

/**
 * Parse a Git LFS pointer, returning its fields or null when the input isn't a
 * (well-formed) pointer. Follows the spec's shape: the first line is the
 * `version` directive, and `oid`/`size` directives are present.
 *
 * @param {Uint8Array|string} input
 * @returns {?LfsPointer}
 */
export function parseLfsPointer(input) {
  const text = pointerText(input);
  if (!text || text.indexOf(SPEC_PREFIX) === -1) return null;

  const fields = new Map();
  const lines = text.split('\n');
  for (const line of lines) {
    if (line === '') continue;
    const space = line.indexOf(' ');
    if (space === -1) return null; // every directive is "key value"
    fields.set(line.slice(0, space), line.slice(space + 1).trim());
  }

  const version = fields.get('version');
  const oid = fields.get('oid');
  const size = fields.get('size');
  if (!version || !version.startsWith(SPEC_PREFIX)) return null;
  // Per spec the first non-empty line must be the version directive.
  if (!lines[0] || !lines[0].startsWith('version ')) return null;
  if (!oid || !/^[\w.-]+:[0-9a-f]+$/i.test(oid)) return null;
  if (!size || !/^\d+$/.test(size)) return null;

  return { version, oid, size: parseInt(size, 10) };
}

/**
 * Whether the given bytes/text are a Git LFS pointer.
 *
 * @param {Uint8Array|string} input
 * @returns {boolean}
 */
export function isLfsPointer(input) {
  return parseLfsPointer(input) !== null;
}

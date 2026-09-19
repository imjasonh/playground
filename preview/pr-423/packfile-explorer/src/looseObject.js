// Build a git loose-object file from resolved content, for export.
//
// A loose object on disk is `zlib(deflate("<type> <len>\0" + content))`, stored
// under `.git/objects/ab/cdef…`. Reconstructing it lets you download an object
// from the pack and drop it straight into a repo, or feed it to `git cat-file`.

import { concatBytes, encodeUtf8 } from "./hex.js";

/** The uncompressed loose-object pre-image (`"<type> <len>\0" + content`). */
export function loosePreimage(typeName, content) {
  return concatBytes([encodeUtf8(`${typeName} ${content.length}\0`), content]);
}

/**
 * Build the on-disk loose-object bytes (zlib-deflated pre-image).
 *
 * `deflate(bytes)` is the raw zlib deflate (for example `pako.deflate`).
 */
export function looseObjectBytes(typeName, content, deflate) {
  return deflate(loosePreimage(typeName, content));
}

/** The loose-object path git would store this oid at (`ab/cdef…`). */
export function looseObjectPath(oid) {
  return `${oid.slice(0, 2)}/${oid.slice(2)}`;
}

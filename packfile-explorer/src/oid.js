// Compute git object ids (SHA-1 of the loose object pre-image).
//
// A git oid is `sha1("<type> <length>\0" + content)`. The actual hashing is
// injected so the parser stays runtime-agnostic: the browser passes a
// `crypto.subtle`-backed digest, tests pass a node:crypto one.

import { bytesToHex, concatBytes, encodeUtf8 } from "./hex.js";

/** Build the loose-object pre-image that git hashes to form the oid. */
export function loosePreimage(typeName, data) {
  const header = encodeUtf8(`${typeName} ${data.length}\0`);
  return concatBytes([header, data]);
}

/**
 * Build a `computeOid(typeName, data)` function from a raw SHA-1 digest.
 *
 * `digest(bytes)` returns a 20-byte `Uint8Array` (or a promise of one).
 */
export function makeComputeOid(digest) {
  return async (typeName, data) => {
    if (data == null) return null;
    const hash = await digest(loosePreimage(typeName, data));
    return bytesToHex(hash);
  };
}

/** A `computeOid` backed by Web Crypto (`crypto.subtle`). */
export function subtleComputeOid(subtle) {
  return makeComputeOid(async (bytes) => new Uint8Array(await subtle.digest("SHA-1", bytes)));
}

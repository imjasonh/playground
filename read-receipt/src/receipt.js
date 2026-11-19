// Builds and checks receipt links. A receipt link carries the doc, how long the
// reading took, when it finished, and a hash of all three with a secret only
// this page knows.
//
// The secret ships in this file, so anyone who reads the source can forge a
// receipt. The hash stops casual edits to the doc or the time, not a
// determined forger.

const SECRET = '48151623429108';

/**
 * The newest receipt format. Version 1 had no finish time; those links still
 * verify.
 */
const VERSION = '2';

/**
 * @param {!Uint8Array} bytes
 * @return {string} Unpadded base64url.
 */
function toBase64Url(bytes) {
  let binary = '';
  // fromCharCode takes its arguments on the stack, so pass them in chunks.
  for (let i = 0; i < bytes.length; i += 0x8000) {
    binary += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  }
  return btoa(binary)
    .replace(/\+/g, '-')
    .replace(/\//g, '_')
    .replace(/=+$/, '');
}

/**
 * @param {string} text Base64url, padded or not.
 * @return {!Uint8Array}
 * @throws {!Error} When `text` isn't base64url.
 */
function fromBase64Url(text) {
  if (!/^[A-Za-z0-9_-]*={0,2}$/.test(text)) {
    throw new Error('not base64url');
  }
  const binary = atob(text.replace(/-/g, '+').replace(/_/g, '/'));
  return Uint8Array.from(binary, (c) => c.charCodeAt(0));
}

/**
 * @param {!Uint8Array} bytes
 * @param {!CompressionStream|!DecompressionStream} stream
 * @return {!Promise<!Uint8Array>}
 */
async function pipe(bytes, stream) {
  const out = new Blob([bytes]).stream().pipeThrough(stream);
  return new Uint8Array(await new Response(out).arrayBuffer());
}

/**
 * Compresses Markdown into a string that's safe in a URL fragment.
 * @param {string} markdown
 * @return {!Promise<string>}
 */
export async function encodeDoc(markdown) {
  const bytes = new TextEncoder().encode(markdown);
  return toBase64Url(await pipe(bytes, new CompressionStream('deflate-raw')));
}

/**
 * Reverses `encodeDoc`.
 * @param {string} encoded
 * @return {!Promise<string>}
 * @throws {!Error} When `encoded` isn't a doc from `encodeDoc`.
 */
export async function decodeDoc(encoded) {
  const bytes = await pipe(
    fromBase64Url(encoded),
    new DecompressionStream('deflate-raw'),
  );
  return new TextDecoder('utf-8', {fatal: true}).decode(bytes);
}

/**
 * Hashes the secret and `fields`, one per line.
 * @param {!Array<string|number>} fields
 * @return {!Promise<string>} The first 128 bits of the SHA-256, in hex.
 */
async function proof(fields) {
  const message = [SECRET, ...fields].join('\n');
  const digest = await crypto.subtle.digest(
    'SHA-256',
    new TextEncoder().encode(message),
  );
  return Array.from(new Uint8Array(digest).subarray(0, 16), (b) =>
    b.toString(16).padStart(2, '0'),
  ).join('');
}

/**
 * Hashes a doc, its reading time, and its finish time with the secret.
 * @param {string} markdown
 * @param {number} seconds
 * @param {number} finished Seconds since the epoch.
 * @return {!Promise<string>} The first 128 bits of the SHA-256, in hex.
 */
export function sign(markdown, seconds, finished) {
  return proof([VERSION, seconds, finished, markdown]);
}

/**
 * Builds the fragment of a receipt link, without the leading `#`.
 * @param {string} markdown
 * @param {number} seconds
 * @param {number} finished Seconds since the epoch.
 * @return {!Promise<string>}
 */
export async function receiptHash(markdown, seconds, finished) {
  const params = new URLSearchParams({
    v: VERSION,
    t: String(seconds),
    f: String(finished),
    p: await sign(markdown, seconds, finished),
    d: await encodeDoc(markdown),
  });
  return params.toString();
}

/**
 * @param {?string} text
 * @return {number} `text` as a whole number, or NaN.
 */
function wholeNumber(text) {
  return text && /^\d{1,15}$/.test(text) ? Number(text) : NaN;
}

/**
 * Reads a receipt from a URL fragment.
 * @param {string} hash `location.hash`, with or without the leading `#`.
 * @return {!Promise<?{markdown: string, seconds: number, finished: ?Date,
 *     verified: boolean}>} The receipt, or null when the fragment has no doc
 *     in it. `seconds` and `finished` are 0 and null unless the receipt
 *     verified, and `finished` is null for a version 1 receipt. Throws when
 *     the fragment has a doc that can't be read.
 */
export async function readReceipt(hash) {
  const params = new URLSearchParams(hash.replace(/^#/, ''));
  const doc = params.get('d');
  if (!doc) return null;
  const markdown = await decodeDoc(doc);
  const seconds = wholeNumber(params.get('t'));
  const finished = wholeNumber(params.get('f'));
  const version = params.get('v');
  let expected = null;
  if (version === VERSION && !isNaN(seconds) && !isNaN(finished)) {
    expected = await sign(markdown, seconds, finished);
  } else if (version === '1' && !isNaN(seconds)) {
    expected = await proof(['1', seconds, markdown]);
  }
  if (expected === null || params.get('p') !== expected) {
    return {markdown, seconds: 0, finished: null, verified: false};
  }
  return {
    markdown,
    seconds,
    finished: version === VERSION ? new Date(finished * 1000) : null,
    verified: true,
  };
}

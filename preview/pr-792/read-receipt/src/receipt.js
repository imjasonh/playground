// Builds and checks receipt links. A receipt link carries the doc, how long the
// reading took, and a hash of both with a secret only this page knows.
//
// The secret ships in this file, so anyone who reads the source can forge a
// receipt. The hash stops casual edits to the doc or the time, not a
// determined forger.

const SECRET = '48151623429108';

/** The newest receipt format. */
const VERSION = '1';

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
 * Hashes a doc and its reading time with the secret.
 * @param {string} markdown
 * @param {number} seconds
 * @return {!Promise<string>} The first 128 bits of the SHA-256, in hex.
 */
export async function sign(markdown, seconds) {
  const message = `${SECRET}\n${VERSION}\n${seconds}\n${markdown}`;
  const digest = await crypto.subtle.digest(
    'SHA-256',
    new TextEncoder().encode(message),
  );
  return Array.from(new Uint8Array(digest).subarray(0, 16), (b) =>
    b.toString(16).padStart(2, '0'),
  ).join('');
}

/**
 * Builds the fragment of a receipt link, without the leading `#`.
 * @param {string} markdown
 * @param {number} seconds
 * @return {!Promise<string>}
 */
export async function receiptHash(markdown, seconds) {
  const params = new URLSearchParams({
    v: VERSION,
    t: String(seconds),
    p: await sign(markdown, seconds),
    d: await encodeDoc(markdown),
  });
  return params.toString();
}

/**
 * Reads a receipt from a URL fragment.
 * @param {string} hash `location.hash`, with or without the leading `#`.
 * @return {!Promise<?{markdown: string, seconds: number, verified: boolean}>}
 *     The receipt, or null when the fragment has no doc in it. Throws when
 *     the fragment has a doc that can't be read.
 */
export async function readReceipt(hash) {
  const params = new URLSearchParams(hash.replace(/^#/, ''));
  const doc = params.get('d');
  if (!doc) return null;
  const markdown = await decodeDoc(doc);
  const time = params.get('t') ?? '';
  const seconds = /^\d+$/.test(time) ? Number(time) : NaN;
  const verified =
    params.get('v') === VERSION &&
    Number.isSafeInteger(seconds) &&
    params.get('p') === (await sign(markdown, seconds));
  return {markdown, seconds: verified ? seconds : 0, verified};
}

// Hex and byte helpers shared by the packfile parser and the UI.

const HEX = [];
for (let i = 0; i < 256; i += 1) {
  HEX.push(i.toString(16).padStart(2, "0"));
}

/** Encode bytes as a lowercase hex string. */
export function bytesToHex(bytes) {
  let out = "";
  for (let i = 0; i < bytes.length; i += 1) {
    out += HEX[bytes[i]];
  }
  return out;
}

/** Decode a hex string into a Uint8Array. Length must be even. */
export function hexToBytes(hex) {
  if (hex.length % 2 !== 0) {
    throw new Error(`odd-length hex string: ${hex.length}`);
  }
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i += 1) {
    out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8", { fatal: false });

/** UTF-8 encode a string to bytes. */
export function encodeUtf8(str) {
  return encoder.encode(str);
}

/** UTF-8 decode bytes to a string (lossy). */
export function decodeUtf8(bytes) {
  return decoder.decode(bytes);
}

/** Concatenate a list of Uint8Arrays into one. */
export function concatBytes(chunks) {
  let total = 0;
  for (const c of chunks) total += c.length;
  const out = new Uint8Array(total);
  let at = 0;
  for (const c of chunks) {
    out.set(c, at);
    at += c.length;
  }
  return out;
}

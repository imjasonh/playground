// Sniff common image formats from blob bytes so image blobs get a preview.

import { decodeUtf8 } from "./hex.js";

function startsWith(bytes, sig, offset = 0) {
  if (bytes.length < offset + sig.length) return false;
  for (let i = 0; i < sig.length; i += 1) {
    if (bytes[offset + i] !== sig[i]) return false;
  }
  return true;
}

/**
 * Detect an image MIME type from magic bytes, or null.
 *
 * Covers PNG, JPEG, GIF, WebP, BMP, and (by a lightweight text sniff) SVG —
 * the formats a browser `<img>` can render from a data URL.
 */
export function detectImage(bytes) {
  if (!bytes || bytes.length < 4) return null;
  if (startsWith(bytes, [0x89, 0x50, 0x4e, 0x47])) return "image/png";
  if (startsWith(bytes, [0xff, 0xd8, 0xff])) return "image/jpeg";
  if (startsWith(bytes, [0x47, 0x49, 0x46, 0x38])) return "image/gif";
  if (startsWith(bytes, [0x42, 0x4d])) return "image/bmp";
  if (
    startsWith(bytes, [0x52, 0x49, 0x46, 0x46]) &&
    startsWith(bytes, [0x57, 0x45, 0x42, 0x50], 8)
  ) {
    return "image/webp";
  }
  const head = decodeUtf8(bytes.subarray(0, 400)).trim().toLowerCase();
  if (head.startsWith("<?xml") ? head.includes("<svg") : head.startsWith("<svg")) {
    return "image/svg+xml";
  }
  return null;
}

/** Base64-encode bytes without Node/DOM-specific helpers. */
export function toBase64(bytes) {
  const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  let out = "";
  let i = 0;
  for (; i + 3 <= bytes.length; i += 3) {
    const n = (bytes[i] << 16) | (bytes[i + 1] << 8) | bytes[i + 2];
    out += chars[(n >> 18) & 63] + chars[(n >> 12) & 63] + chars[(n >> 6) & 63] + chars[n & 63];
  }
  const rem = bytes.length - i;
  if (rem === 1) {
    const n = bytes[i] << 16;
    out += chars[(n >> 18) & 63] + chars[(n >> 12) & 63] + "==";
  } else if (rem === 2) {
    const n = (bytes[i] << 16) | (bytes[i + 1] << 8);
    out += chars[(n >> 18) & 63] + chars[(n >> 12) & 63] + chars[(n >> 6) & 63] + "=";
  }
  return out;
}

/** Build a data URL for an image blob, or null if it isn't a known image. */
export function imageDataUrl(bytes) {
  const mime = detectImage(bytes);
  if (!mime) return null;
  return `data:${mime};base64,${toBase64(bytes)}`;
}

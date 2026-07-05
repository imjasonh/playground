// Serverless signaling helpers for LinkChat.
//
// WebRTC needs peers to exchange session descriptions (SDP) before a
// connection can form. Normally a signaling *server* relays these. LinkChat
// has no backend, so instead we pack a session description into a compact,
// URL-safe token that a human can share (as a link, or pasted into a box).
//
// These functions are pure and DOM-free so they can be unit tested under Node
// and reused in the browser. They rely only on Web-standard globals
// (`btoa`/`atob`, `TextEncoder`/`TextDecoder`) that exist in both environments.

import { deflateToBase64Url, inflateFromBase64Url } from "./codec.js";

export const SIGNAL_VERSION = 1;

// Hash keys used in links. `c` carries a plain (uncompressed) token; `z`
// carries a DEFLATE-compressed token. A single key type is used for both
// offers and answers; the decoded payload records which it is. Compressed (`z`)
// is the default now — it keeps links short enough to fit in a QR code — but
// plain `c` links are still accepted for backward compatibility.
export const LINK_KEY = "c";
export const COMPRESSED_KEY = "z";

function toBase64Url(bytes) {
  let binary = "";
  for (let i = 0; i < bytes.length; i += 1) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary)
    .replace(/\+/g, "-")
    .replace(/\//g, "_")
    .replace(/=+$/, "");
}

function fromBase64Url(token) {
  const normalized = token.replace(/-/g, "+").replace(/_/g, "/");
  const padded = normalized + "=".repeat((4 - (normalized.length % 4)) % 4);
  const binary = atob(padded);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i += 1) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

// Encode a session description ({ type, sdp }) into a URL-safe token.
export function encodeSignal(description) {
  if (!description || typeof description !== "object") {
    throw new TypeError("encodeSignal expects a session description object");
  }
  const { type, sdp } = description;
  if (type !== "offer" && type !== "answer") {
    throw new TypeError(`unsupported description type: ${String(type)}`);
  }
  if (typeof sdp !== "string" || sdp.length === 0) {
    throw new TypeError("session description is missing sdp");
  }
  const payload = { v: SIGNAL_VERSION, t: type, s: sdp };
  const json = JSON.stringify(payload);
  const bytes = new TextEncoder().encode(json);
  return toBase64Url(bytes);
}

// Decode a token produced by encodeSignal back into { type, sdp }. Throws on
// anything malformed so callers can surface a clear error.
export function decodeSignal(token) {
  if (typeof token !== "string" || token.length === 0) {
    throw new TypeError("decodeSignal expects a non-empty token");
  }
  const bytes = fromBase64Url(token.trim());
  const json = new TextDecoder().decode(bytes);
  const payload = JSON.parse(json);
  if (!payload || typeof payload !== "object") {
    throw new Error("token did not contain a signaling payload");
  }
  if (payload.v !== SIGNAL_VERSION) {
    throw new Error(`unsupported signaling version: ${String(payload.v)}`);
  }
  if (payload.t !== "offer" && payload.t !== "answer") {
    throw new Error(`unsupported description type: ${String(payload.t)}`);
  }
  if (typeof payload.s !== "string" || payload.s.length === 0) {
    throw new Error("token is missing sdp");
  }
  return { type: payload.t, sdp: payload.s };
}

// Like decodeSignal but returns null instead of throwing.
export function safeDecodeSignal(token) {
  try {
    return decodeSignal(token);
  } catch {
    return null;
  }
}

// Build the JSON payload string that both encoders share.
function payloadJson(description) {
  if (!description || typeof description !== "object") {
    throw new TypeError("expected a session description object");
  }
  const { type, sdp } = description;
  if (type !== "offer" && type !== "answer") {
    throw new TypeError(`unsupported description type: ${String(type)}`);
  }
  if (typeof sdp !== "string" || sdp.length === 0) {
    throw new TypeError("session description is missing sdp");
  }
  return JSON.stringify({ v: SIGNAL_VERSION, t: type, s: sdp });
}

function parsePayloadJson(json) {
  const payload = JSON.parse(json);
  if (!payload || typeof payload !== "object") {
    throw new Error("token did not contain a signaling payload");
  }
  if (payload.v !== SIGNAL_VERSION) {
    throw new Error(`unsupported signaling version: ${String(payload.v)}`);
  }
  if (payload.t !== "offer" && payload.t !== "answer") {
    throw new Error(`unsupported description type: ${String(payload.t)}`);
  }
  if (typeof payload.s !== "string" || payload.s.length === 0) {
    throw new Error("token is missing sdp");
  }
  return { type: payload.t, sdp: payload.s };
}

// Encode a session description into a compact, DEFLATE-compressed token.
export async function encodeSignalCompressed(description) {
  return deflateToBase64Url(payloadJson(description));
}

// Decode a compressed token back into { type, sdp }.
export async function decodeSignalCompressed(token) {
  return parsePayloadJson(await inflateFromBase64Url(token));
}

// Decode a token of either flavor. Compressed tokens are DEFLATE streams that
// are not valid JSON, so we try the plain path first (cheap and synchronous),
// then fall back to decompression. Returns { type, sdp } or throws.
export async function decodeAnySignal(token) {
  const plain = safeDecodeSignal(token);
  if (plain) return plain;
  return decodeSignalCompressed(token);
}

// Build a shareable link that embeds a signaling token in the URL hash. The
// hash is used (not the query string) so the token never leaves the browser —
// hash fragments are not sent to any server.
export function buildLink(baseUrl, token, key = LINK_KEY) {
  if (typeof baseUrl !== "string" || baseUrl.length === 0) {
    throw new TypeError("buildLink expects a base URL");
  }
  if (typeof token !== "string" || token.length === 0) {
    throw new TypeError("buildLink expects a token");
  }
  const withoutHash = baseUrl.split("#")[0];
  return `${withoutHash}#${key}=${token}`;
}

// Build a compressed invite/answer link (`#z=…`).
export async function buildCompressedLink(baseUrl, description) {
  const token = await encodeSignalCompressed(description);
  return buildLink(baseUrl, token, COMPRESSED_KEY);
}

// Pull a signaling token out of a full URL's hash, preferring the compressed
// (`z`) key and falling back to the plain (`c`) key. Returns null if absent.
export function tokenFromUrl(url) {
  if (typeof url !== "string") return null;
  const hashIndex = url.indexOf("#");
  if (hashIndex === -1) return null;
  const hash = url.slice(hashIndex + 1);
  const params = new URLSearchParams(hash);
  const token = params.get(COMPRESSED_KEY) || params.get(LINK_KEY);
  return token && token.length > 0 ? token : null;
}

// Accept whatever a user pastes — a full invite link or a bare token — and
// return just the token. Returns null when nothing usable is found.
export function extractToken(input) {
  if (typeof input !== "string") return null;
  const trimmed = input.trim();
  if (trimmed.length === 0) return null;
  if (trimmed.includes("#")) {
    const fromHash = tokenFromUrl(trimmed);
    if (fromHash) return fromHash;
  }
  // Otherwise assume the whole string is the token itself.
  return trimmed;
}

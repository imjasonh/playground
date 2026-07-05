// Compression codec for LinkChat signaling payloads.
//
// A WebRTC session description is several kilobytes of highly repetitive text
// (codec lists, ICE candidates). That's far too big for a QR code, whose
// hard ceiling is ~2953 bytes. DEFLATE shrinks a typical description by ~4x,
// which brings the shareable payload down to a size that both fits in a QR and
// keeps the copyable link short.
//
// Uses the Web-standard Compression Streams API (`CompressionStream`), which is
// available in modern browsers and in Node (>= 18), so this module is
// isomorphic and unit-testable without a DOM.

const FORMAT = "deflate-raw";

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

async function pipeThrough(bytes, stream) {
  const writer = stream.writable.getWriter();
  writer.write(bytes);
  writer.close();
  const chunks = [];
  const reader = stream.readable.getReader();
  for (;;) {
    const { value, done } = await reader.read();
    if (done) break;
    chunks.push(value);
  }
  let total = 0;
  for (const c of chunks) total += c.length;
  const out = new Uint8Array(total);
  let offset = 0;
  for (const c of chunks) {
    out.set(c, offset);
    offset += c.length;
  }
  return out;
}

// Compress a string and return a URL-safe base64 token.
export async function deflateToBase64Url(text) {
  const input = new TextEncoder().encode(text);
  const compressed = await pipeThrough(input, new CompressionStream(FORMAT));
  return toBase64Url(compressed);
}

// Inverse of deflateToBase64Url. Throws on malformed input.
export async function inflateFromBase64Url(token) {
  if (typeof token !== "string" || token.length === 0) {
    throw new TypeError("inflateFromBase64Url expects a non-empty token");
  }
  const bytes = fromBase64Url(token.trim());
  const decompressed = await pipeThrough(bytes, new DecompressionStream(FORMAT));
  return new TextDecoder().decode(decompressed);
}

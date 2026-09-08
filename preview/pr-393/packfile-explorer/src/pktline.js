// The git pkt-line framing used by the smart-HTTP transport.
//
// A pkt-line is a 4-byte hex length prefix (the length counts the 4 prefix
// bytes) followed by that many bytes of payload. Two prefixes are special:
// `0000` is a flush packet and `0001` is a delimiter (protocol v2). See
// https://git-scm.com/docs/protocol-common#_pkt_line_format.

import { concatBytes, decodeUtf8, encodeUtf8 } from "./hex.js";

export const PKT_FLUSH = { kind: "flush" };
export const PKT_DELIM = { kind: "delim" };

/**
 * Split a byte stream into pkt-lines.
 *
 * Returns an array of entries: `{ kind: "flush" }`, `{ kind: "delim" }`, or
 * `{ kind: "data", data: Uint8Array }`. Trailing bytes that don't form a whole
 * pkt-line are ignored (the server always ends cleanly).
 */
export function decodePktLines(bytes) {
  const lines = [];
  let at = 0;
  while (at + 4 <= bytes.length) {
    const header = decodeUtf8(bytes.subarray(at, at + 4));
    if (!/^[0-9a-fA-F]{4}$/.test(header)) {
      throw new Error(`invalid pkt-line length at byte ${at}: ${header}`);
    }
    const len = parseInt(header, 16);
    if (len === 0) {
      lines.push(PKT_FLUSH);
      at += 4;
      continue;
    }
    if (len === 1) {
      lines.push(PKT_DELIM);
      at += 4;
      continue;
    }
    if (len < 4 || at + len > bytes.length) {
      throw new Error(`truncated pkt-line at byte ${at}: length ${len}`);
    }
    lines.push({ kind: "data", data: bytes.subarray(at + 4, at + len) });
    at += len;
  }
  return lines;
}

/** Encode a payload (string or bytes) as one pkt-line. */
export function encodePktLine(payload) {
  const body = typeof payload === "string" ? encodeUtf8(payload) : payload;
  const len = body.length + 4;
  if (len > 0xffff) {
    throw new Error(`pkt-line too long: ${len}`);
  }
  const header = encodeUtf8(len.toString(16).padStart(4, "0"));
  return concatBytes([header, body]);
}

/** The flush packet (`0000`). */
export function flushPkt() {
  return encodeUtf8("0000");
}

/**
 * Incremental upload-pack response reader for streaming fetches.
 *
 * Combines the control/side-band split with side-band demux so progress can be
 * reported live as chunks arrive. Feed response bytes to `push`; it drains
 * whole pkt-lines, routes control lines, pack data (band 1), progress (band 2),
 * and errors (band 3), and calls `onProgress(text)` as progress arrives. Call
 * `finish()` for `{ pack, progress, error, control }`.
 */
export function createUploadPackReader({ onProgress = null } = {}) {
  let buffer = new Uint8Array(0);
  let inPack = false;
  const control = [];
  const packChunks = [];
  let progress = "";
  let error = "";

  function handleLine(line) {
    if (!inPack) {
      if (line.kind === "flush") {
        inPack = true;
        return;
      }
      if (line.kind === "data") {
        const text = decodeUtf8(line.data).replace(/\n$/, "");
        if (line.data.length > 0 && line.data[0] <= 3 && !/^[A-Za-z]/.test(text)) {
          inPack = true;
        } else {
          control.push(text);
          return;
        }
      } else {
        return;
      }
    }
    if (line.kind !== "data" || line.data.length === 0) return;
    const band = line.data[0];
    const rest = line.data.subarray(1);
    if (band === 1) {
      packChunks.push(rest.slice());
    } else if (band === 2) {
      const text = decodeUtf8(rest);
      progress += text;
      if (onProgress) onProgress(text);
    } else if (band === 3) {
      error += decodeUtf8(rest);
    }
  }

  return {
    push(chunk) {
      buffer = buffer.length === 0 ? chunk : concatBytes([buffer, chunk]);
      let at = 0;
      while (at + 4 <= buffer.length) {
        const header = decodeUtf8(buffer.subarray(at, at + 4));
        if (!/^[0-9a-fA-F]{4}$/.test(header)) {
          throw new Error(`invalid pkt-line length at byte ${at}: ${header}`);
        }
        const len = parseInt(header, 16);
        if (len === 0) {
          handleLine(PKT_FLUSH);
          at += 4;
          continue;
        }
        if (len === 1) {
          handleLine(PKT_DELIM);
          at += 4;
          continue;
        }
        if (len < 4) throw new Error(`invalid pkt-line length ${len} at byte ${at}`);
        if (at + len > buffer.length) break; // wait for more bytes
        handleLine({ kind: "data", data: buffer.subarray(at + 4, at + len) });
        at += len;
      }
      buffer = buffer.subarray(at);
    },
    finish() {
      return { pack: concatBytes(packChunks), progress, error, control };
    },
  };
}

/** Demultiplex a side-band-64k stream.
 *
 * Each data pkt-line starts with a band byte: 1 = pack data, 2 = progress,
 * 3 = fatal error. Returns the concatenated pack bytes plus decoded progress
 * and error text.
 */
export function demuxSideband(lines) {
  const packChunks = [];
  let progress = "";
  let error = "";
  for (const line of lines) {
    if (line.kind !== "data" || line.data.length === 0) continue;
    const band = line.data[0];
    const rest = line.data.subarray(1);
    if (band === 1) packChunks.push(rest);
    else if (band === 2) progress += decodeUtf8(rest);
    else if (band === 3) error += decodeUtf8(rest);
  }
  return { pack: concatBytes(packChunks), progress, error };
}

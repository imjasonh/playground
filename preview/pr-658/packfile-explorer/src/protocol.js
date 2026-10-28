// Smart-HTTP upload-pack request and response helpers (protocol v0/v1).
//
// The explorer fetches a repository's packfile with the two-step smart-HTTP
// dance: GET info/refs to learn the refs, then POST git-upload-pack with a set
// of `want` lines. See https://git-scm.com/docs/http-protocol.

import { concatBytes, decodeUtf8 } from "./hex.js";
import { decodePktLines, encodePktLine, flushPkt } from "./pktline.js";

/** Client capabilities requested on the first `want` line. */
export const CLIENT_CAPABILITIES = [
  "multi_ack_detailed",
  "side-band-64k",
  "ofs-delta",
  "thin-pack",
  "no-progress",
  "agent=packfile-explorer",
];

const OID_RE = /^[0-9a-f]{40}$/;

/**
 * Parse an info/refs advertisement (`service=git-upload-pack`).
 *
 * Returns `{ refs: [{ oid, name }], capabilities: [string], head }`. `head` is
 * the oid the symref `HEAD` points at, when advertised.
 */
export function parseInfoRefs(bytes) {
  const lines = decodePktLines(bytes);
  const refs = [];
  let capabilities = [];
  let sawService = false;
  let head = null;

  for (const line of lines) {
    if (line.kind !== "data") continue;
    const text = decodeUtf8(line.data).replace(/\n$/, "");
    if (text.startsWith("# service=")) {
      sawService = true;
      continue;
    }
    // The first ref line carries capabilities after a NUL byte.
    const nul = text.indexOf("\0");
    let refPart = text;
    if (nul !== -1) {
      refPart = text.slice(0, nul);
      capabilities = text.slice(nul + 1).split(" ").filter(Boolean);
    }
    const sp = refPart.indexOf(" ");
    if (sp === -1) continue;
    const oid = refPart.slice(0, sp);
    const name = refPart.slice(sp + 1);
    if (!OID_RE.test(oid)) continue;
    refs.push({ oid, name });
  }

  for (const cap of capabilities) {
    if (cap.startsWith("symref=HEAD:")) {
      const target = cap.slice("symref=HEAD:".length);
      const match = refs.find((r) => r.name === target);
      if (match) head = match.oid;
    }
  }
  if (!head) {
    const headRef = refs.find((r) => r.name === "HEAD");
    if (headRef) head = headRef.oid;
  }

  return { refs, capabilities, head, sawService };
}

/**
 * Build the body of a POST git-upload-pack request.
 *
 * `wants` is a list of oids to request. `deepen` (optional) requests a shallow
 * clone at that depth, which keeps the pack small for exploration.
 */
export function buildFetchRequest({ wants, deepen = null, capabilities = CLIENT_CAPABILITIES }) {
  if (!wants || wants.length === 0) {
    throw new Error("buildFetchRequest needs at least one want");
  }
  const chunks = [];
  wants.forEach((oid, i) => {
    const caps = i === 0 ? ` ${capabilities.join(" ")}` : "";
    chunks.push(encodePktLine(`want ${oid}${caps}\n`));
  });
  if (deepen != null) {
    chunks.push(encodePktLine(`deepen ${deepen}\n`));
  }
  chunks.push(flushPkt());
  chunks.push(encodePktLine("done\n"));
  return concatBytes(chunks);
}

/**
 * Split an upload-pack result into its acknowledgement preamble and the
 * side-band pack stream.
 *
 * The server sends `shallow`/`unshallow`/`ACK`/`NAK` control pkt-lines, then a
 * flush, then the side-band packet stream. Returns `{ control, sidebandLines }`
 * where `control` is the parsed control text lines and `sidebandLines` are the
 * remaining data pkt-lines to hand to `demuxSideband`.
 */
export function splitUploadPackResult(bytes) {
  const lines = decodePktLines(bytes);
  const control = [];
  const sidebandLines = [];
  let inPack = false;
  for (const line of lines) {
    if (!inPack) {
      if (line.kind === "flush") {
        inPack = true;
        continue;
      }
      if (line.kind === "data") {
        const text = decodeUtf8(line.data).replace(/\n$/, "");
        // A side-band pack packet begins with band byte 0x01/0x02/0x03; control
        // lines are plain ASCII words. Once we see a band byte we're in the pack.
        if (line.data[0] <= 3 && !/^[A-Za-z]/.test(text)) {
          inPack = true;
          sidebandLines.push(line);
        } else {
          control.push(text);
        }
      }
      continue;
    }
    sidebandLines.push(line);
  }
  return { control, sidebandLines };
}

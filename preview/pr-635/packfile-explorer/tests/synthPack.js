// Build synthetic packfiles in tests so delta resolution (both ofs- and
// ref-delta) is exercised deterministically without git.

import { deflateSync } from "node:zlib";
import { createHash } from "node:crypto";
import {
  OBJ_BLOB,
  OBJ_OFS_DELTA,
  OBJ_REF_DELTA,
} from "../src/pack.js";
import { concatBytes } from "../src/hex.js";

/** SHA-1 hex of the loose pre-image, matching git's oid. */
export function oidOf(typeName, content) {
  const header = Buffer.from(`${typeName} ${content.length}\0`);
  return createHash("sha1").update(Buffer.concat([header, Buffer.from(content)])).digest("hex");
}

function encodeEntryHeader(type, size) {
  const bytes = [];
  let first = (type << 4) | (size & 0x0f);
  let rest = Math.floor(size / 16);
  if (rest > 0) first |= 0x80;
  bytes.push(first);
  while (rest > 0) {
    let c = rest & 0x7f;
    rest = Math.floor(rest / 128);
    if (rest > 0) c |= 0x80;
    bytes.push(c);
  }
  return Uint8Array.from(bytes);
}

// Inverse of readOffsetVarint in src/pack.js (git's pack-write.c encoding).
function encodeOffset(offset) {
  const bytes = [offset & 0x7f];
  let o = Math.floor(offset / 128);
  while (o > 0) {
    o -= 1;
    bytes.push(0x80 | (o & 0x7f));
    o = Math.floor(o / 128);
  }
  bytes.reverse();
  return Uint8Array.from(bytes);
}

function encodeDeltaSize(n) {
  const bytes = [];
  let v = n;
  do {
    let c = v & 0x7f;
    v = Math.floor(v / 128);
    if (v > 0) c |= 0x80;
    bytes.push(c);
  } while (v > 0);
  return Uint8Array.from(bytes);
}

/**
 * Build a delta that emits `copy(base)` then `insert(suffix)`, turning `base`
 * into `base + suffix`.
 */
export function buildAppendDelta(base, suffix) {
  const parts = [encodeDeltaSize(base.length), encodeDeltaSize(base.length + suffix.length)];
  // Copy the whole base: offset 0 (no offset bytes), size = base.length.
  const size = base.length;
  let opcode = 0x80;
  const sizeBytes = [];
  if (size & 0xff) {
    opcode |= 0x10;
    sizeBytes.push(size & 0xff);
  }
  if ((size >> 8) & 0xff) {
    opcode |= 0x20;
    sizeBytes.push((size >> 8) & 0xff);
  }
  if ((size >> 16) & 0xff) {
    opcode |= 0x40;
    sizeBytes.push((size >> 16) & 0xff);
  }
  parts.push(Uint8Array.from([opcode, ...sizeBytes]));
  // Insert the suffix (length must fit in one insert op for the test).
  const suf = Buffer.from(suffix);
  parts.push(Uint8Array.from([suf.length]));
  parts.push(new Uint8Array(suf));
  return concatBytes(parts);
}

/**
 * Assemble a packfile from a list of entries. Each entry is one of:
 *   { type: "blob", content }
 *   { type: "ofs-delta", delta, baseIndex }
 *   { type: "ref-delta", delta, baseOid }
 * Returns `{ pack, entries }` where entries carry their byte offsets.
 */
export function buildPack(specs) {
  const header = new Uint8Array(12);
  header.set(Buffer.from("PACK"), 0);
  new DataView(header.buffer).setUint32(4, 2);
  new DataView(header.buffer).setUint32(8, specs.length);

  const chunks = [header];
  let offset = 12;
  const offsets = [];

  specs.forEach((spec) => {
    offsets.push(offset);
    let head;
    let extra = new Uint8Array(0);
    let payload;
    if (spec.type === "blob") {
      head = encodeEntryHeader(OBJ_BLOB, spec.content.length);
      payload = new Uint8Array(deflateSync(Buffer.from(spec.content)));
    } else if (spec.type === "ofs-delta") {
      head = encodeEntryHeader(OBJ_OFS_DELTA, spec.delta.length);
      const distance = offset - offsets[spec.baseIndex];
      extra = encodeOffset(distance);
      payload = new Uint8Array(deflateSync(Buffer.from(spec.delta)));
    } else if (spec.type === "ref-delta") {
      head = encodeEntryHeader(OBJ_REF_DELTA, spec.delta.length);
      extra = Uint8Array.from(Buffer.from(spec.baseOid, "hex"));
      payload = new Uint8Array(deflateSync(Buffer.from(spec.delta)));
    } else {
      throw new Error(`unknown spec type ${spec.type}`);
    }
    const entry = concatBytes([head, extra, payload]);
    chunks.push(entry);
    offset += entry.length;
  });

  // 20-byte trailer = SHA-1 of everything before it.
  const body = concatBytes(chunks);
  const trailer = createHash("sha1").update(Buffer.from(body)).digest();
  return { pack: concatBytes([body, new Uint8Array(trailer)]), offsets };
}

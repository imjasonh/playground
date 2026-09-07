// Parse a git packfile into its raw entries, then resolve deltas into objects.
//
// Pack format: a 12-byte header ("PACK", version, object count), a sequence of
// variable-length object entries, and a 20-byte SHA-1 trailer over everything
// before it. See https://git-scm.com/docs/pack-format.

import { applyDelta } from "./delta.js";
import { bytesToHex, decodeUtf8 } from "./hex.js";

export const OBJ_COMMIT = 1;
export const OBJ_TREE = 2;
export const OBJ_BLOB = 3;
export const OBJ_TAG = 4;
export const OBJ_OFS_DELTA = 6;
export const OBJ_REF_DELTA = 7;

const TYPE_NAMES = {
  [OBJ_COMMIT]: "commit",
  [OBJ_TREE]: "tree",
  [OBJ_BLOB]: "blob",
  [OBJ_TAG]: "tag",
  [OBJ_OFS_DELTA]: "ofs-delta",
  [OBJ_REF_DELTA]: "ref-delta",
};

/** Map a numeric pack object type to its name. */
export function typeName(type) {
  return TYPE_NAMES[type] || `unknown(${type})`;
}

function readUint32(bytes, at) {
  return (
    ((bytes[at] << 24) | (bytes[at + 1] << 16) | (bytes[at + 2] << 8) | bytes[at + 3]) >>> 0
  );
}

/** Read the type + inflated-size header that prefixes each object entry. */
function readEntryHeader(bytes, start) {
  let at = start;
  let byte = bytes[at++];
  const type = (byte >> 4) & 0x07;
  let size = byte & 0x0f;
  let shift = 4;
  while (byte & 0x80) {
    byte = bytes[at++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { type, size, at };
}

/** Read the negative base offset varint used by OFS_DELTA entries. */
function readOffsetVarint(bytes, start) {
  let at = start;
  let byte = bytes[at++];
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = bytes[at++];
    value = ((value + 1) * 128) + (byte & 0x7f);
  }
  return { value, at };
}

/**
 * Parse a packfile's structure without resolving deltas.
 *
 * `inflate(bytes, offset)` must inflate the zlib stream starting at `offset`
 * and return `{ data, consumed }` where `consumed` is the number of compressed
 * bytes read. Returns `{ version, count, objects, trailer, trailerOffset }`.
 * Each object records its byte offset, type, declared inflated size, the
 * compressed byte count, and the inflated payload (object content, or delta
 * instructions for delta entries).
 */
export function parsePack(bytes, inflate) {
  if (bytes.length < 12 || decodeUtf8(bytes.subarray(0, 4)) !== "PACK") {
    throw new Error("not a packfile: missing PACK signature");
  }
  const version = readUint32(bytes, 4);
  if (version !== 2 && version !== 3) {
    throw new Error(`unsupported pack version ${version}`);
  }
  const count = readUint32(bytes, 8);

  const objects = [];
  let at = 12;
  for (let i = 0; i < count; i += 1) {
    const offset = at;
    const header = readEntryHeader(bytes, at);
    at = header.at;

    let baseOffset = null;
    let baseOid = null;
    if (header.type === OBJ_OFS_DELTA) {
      const ofs = readOffsetVarint(bytes, at);
      at = ofs.at;
      baseOffset = offset - ofs.value;
    } else if (header.type === OBJ_REF_DELTA) {
      baseOid = bytesToHex(bytes.subarray(at, at + 20));
      at += 20;
    }

    const dataOffset = at;
    const { data, consumed } = inflate(bytes, at);
    at += consumed;

    objects.push({
      index: i,
      offset,
      type: header.type,
      typeName: typeName(header.type),
      size: header.size,
      dataOffset,
      packedSize: at - offset,
      compressedSize: consumed,
      baseOffset,
      baseOid,
      data,
    });
  }

  const trailerOffset = at;
  const trailer = bytesToHex(bytes.subarray(at, at + 20));
  return { version, count, objects, trailer, trailerOffset };
}

/**
 * Resolve every delta entry against its base to produce final git objects.
 *
 * `computeOid(typeName, data)` returns the object's 40-char SHA-1 (async is
 * allowed). Returns `{ objects, byOid, byOffset, contentByOid, unresolved }`.
 * Each resolved object has `{ oid, type, typeName, size, offset, packedSize,
 * deltaType, baseOid, depth, index }`; content bytes live in `contentByOid`.
 */
export async function resolveObjects(parsed, computeOid) {
  const byOffset = new Map();
  for (const raw of parsed.objects) byOffset.set(raw.offset, raw);

  const contentByOffset = new Map();
  const finalTypeByOffset = new Map();
  const depthByOffset = new Map();

  // Resolve one raw entry to its undeltified content + base type, memoized.
  const rawByOid = new Map(); // filled lazily as we compute oids

  function resolveRaw(raw, seen) {
    if (contentByOffset.has(raw.offset)) {
      return {
        data: contentByOffset.get(raw.offset),
        type: finalTypeByOffset.get(raw.offset),
        depth: depthByOffset.get(raw.offset),
      };
    }
    if (seen.has(raw.offset)) {
      throw new Error(`delta cycle at offset ${raw.offset}`);
    }
    seen.add(raw.offset);

    if (raw.type !== OBJ_OFS_DELTA && raw.type !== OBJ_REF_DELTA) {
      const result = { data: raw.data, type: raw.type, depth: 0 };
      contentByOffset.set(raw.offset, result.data);
      finalTypeByOffset.set(raw.offset, result.type);
      depthByOffset.set(raw.offset, result.depth);
      return result;
    }

    let base;
    if (raw.type === OBJ_OFS_DELTA) {
      base = byOffset.get(raw.baseOffset);
      if (!base) throw new Error(`missing ofs-delta base at ${raw.baseOffset}`);
    } else {
      base = rawByOid.get(raw.baseOid);
      if (!base) {
        // Thin-pack base not present in this pack.
        const result = { data: null, type: null, depth: -1, thin: true };
        contentByOffset.set(raw.offset, null);
        finalTypeByOffset.set(raw.offset, null);
        depthByOffset.set(raw.offset, -1);
        return result;
      }
    }

    const resolvedBase = resolveRaw(base, seen);
    if (resolvedBase.data == null) {
      contentByOffset.set(raw.offset, null);
      finalTypeByOffset.set(raw.offset, null);
      depthByOffset.set(raw.offset, -1);
      return { data: null, type: null, depth: -1, thin: true };
    }
    const data = applyDelta(resolvedBase.data, raw.data);
    const type = resolvedBase.type;
    const depth = resolvedBase.depth + 1;
    contentByOffset.set(raw.offset, data);
    finalTypeByOffset.set(raw.offset, type);
    depthByOffset.set(raw.offset, depth);
    return { data, type, depth };
  }

  // First pass: resolve all non-ref-delta content so ref-delta bases (by oid)
  // can be found. We compute oids for every fully-resolved object.
  const resolved = [];
  const contentByOid = new Map();
  const byOid = new Map();
  const unresolved = [];

  // Resolve content for entries whose base is reachable by offset (all
  // non-ref-delta chains), computing oids so ref-delta lookups can succeed.
  // We iterate until no further progress is made to handle ref-delta ordering.
  const pending = [...parsed.objects];
  let progress = true;
  while (pending.length > 0 && progress) {
    progress = false;
    const stillPending = [];
    for (const raw of pending) {
      try {
        const r = resolveRaw(raw, new Set());
        if (r.data == null) {
          // ref-delta base not yet known; retry later.
          if (raw.type === OBJ_REF_DELTA && !rawByOid.has(raw.baseOid)) {
            contentByOffset.delete(raw.offset);
            finalTypeByOffset.delete(raw.offset);
            depthByOffset.delete(raw.offset);
            stillPending.push(raw);
            continue;
          }
        }
        const oid = await computeOid(typeName(r.type), r.data);
        raw.oid = oid;
        rawByOid.set(oid, raw);
        contentByOid.set(oid, r.data);
        progress = true;
      } catch (err) {
        stillPending.push(raw);
      }
    }
    if (stillPending.length === pending.length) break;
    pending.length = 0;
    pending.push(...stillPending);
  }

  // Anything still pending is a genuine thin-pack (external base) entry.
  for (const raw of pending) {
    unresolved.push({
      index: raw.index,
      offset: raw.offset,
      typeName: raw.typeName,
      baseOid: raw.baseOid,
    });
  }

  for (const raw of parsed.objects) {
    const data = contentByOffset.get(raw.offset);
    const type = finalTypeByOffset.get(raw.offset);
    const depth = depthByOffset.get(raw.offset);
    const deltaType =
      raw.type === OBJ_OFS_DELTA ? "ofs" : raw.type === OBJ_REF_DELTA ? "ref" : "none";
    let baseOid = null;
    if (deltaType === "ofs") {
      const base = byOffset.get(raw.baseOffset);
      baseOid = base ? base.oid : null;
    } else if (deltaType === "ref") {
      baseOid = raw.baseOid;
    }
    const entry = {
      index: raw.index,
      oid: raw.oid || null,
      offset: raw.offset,
      dataOffset: raw.dataOffset,
      type: type == null ? null : type,
      typeName: type == null ? "unresolved" : typeName(type),
      rawType: raw.type,
      rawTypeName: raw.typeName,
      size: data ? data.length : raw.size,
      declaredSize: raw.size,
      packedSize: raw.packedSize,
      compressedSize: raw.compressedSize,
      deltaType,
      baseOffset: raw.baseOffset,
      baseOid,
      depth: depth == null ? -1 : depth,
    };
    resolved.push(entry);
    if (entry.oid) byOid.set(entry.oid, entry);
  }

  return { objects: resolved, byOid, byOffset, contentByOid, unresolved };
}

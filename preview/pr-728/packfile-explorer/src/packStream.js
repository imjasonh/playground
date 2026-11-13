// Index a packfile by streaming it from a reader, without holding it in memory.
//
// `parsePack` + `resolveObjects` (see pack.js) load the whole pack and keep
// every inflated object. That tops out around a few hundred MiB. This path
// instead reads each entry from a `packReader` on demand, resolves it against a
// bounded delta-base cache, records only per-object metadata (type, sizes,
// delta links, depth, oid), and keeps resident content only for the object
// types the whole-graph views need (commit, tree, tag) — blobs, which dominate
// a pack's bytes, are re-read from the file when inspected (see `lazyContent`).
//
// The produced `objects` entries match `resolveObjects`' shape, so the index,
// stats, reachability, tree-walk, and attribution modules consume them
// unchanged.

import { applyDelta } from "./delta.js";
import {
  OBJ_OFS_DELTA,
  OBJ_REF_DELTA,
  typeName,
} from "./pack.js";
import { bytesToHex, decodeUtf8 } from "./hex.js";

// A single entry header fits easily in this many bytes: a type/size varint,
// then either a 20-byte ref-delta base oid or an ofs-delta offset varint (at
// most ~10 bytes even for a multi-terabyte base distance).
const HEADER_WINDOW = 64;

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

function readOffsetVarint(bytes, start) {
  let at = start;
  let byte = bytes[at++];
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = bytes[at++];
    value = (value + 1) * 128 + (byte & 0x7f);
  }
  return { value, at };
}

/** Read the 12-byte pack header. Returns `{ version, count }`. */
export async function readPackHeader(reader) {
  const head = await reader.read(0, 12);
  if (head.length < 12 || decodeUtf8(head.subarray(0, 4)) !== "PACK") {
    throw new Error("not a packfile: missing PACK signature");
  }
  const view = new DataView(head.buffer, head.byteOffset, 12);
  const version = view.getUint32(4);
  if (version !== 2 && version !== 3) {
    throw new Error(`unsupported pack version ${version}`);
  }
  return { version, count: view.getUint32(8) };
}

/**
 * Read one raw entry at `offset`: its header fields and inflated payload.
 *
 * The payload is the object content for a non-delta entry, or the delta
 * instruction stream for a delta entry. Returns `{ type, declaredSize,
 * dataOffset, data, consumed, packedSize, baseOffset, baseOid }`.
 */
export async function readEntryAt(reader, inflate, offset) {
  const window = await reader.read(offset, Math.min(HEADER_WINDOW, reader.size - offset));
  const header = readEntryHeader(window, 0);
  let at = header.at;
  let baseOffset = null;
  let baseOid = null;
  if (header.type === OBJ_OFS_DELTA) {
    const ofs = readOffsetVarint(window, at);
    at = ofs.at;
    baseOffset = offset - ofs.value;
  } else if (header.type === OBJ_REF_DELTA) {
    baseOid = bytesToHex(window.subarray(at, at + 20));
    at += 20;
  }
  const dataOffset = offset + at;
  const { data, consumed } = await inflate(reader, dataOffset);
  return {
    type: header.type,
    declaredSize: header.size,
    dataOffset,
    data,
    consumed,
    packedSize: at + consumed,
    baseOffset,
    baseOid,
  };
}

// A byte-budgeted LRU of resolved contents, keyed by pack offset, so a delta
// can reuse a base a neighbor just resolved without re-reading the file.
function makeContentCache(budgetBytes) {
  const map = new Map();
  let bytes = 0;
  return {
    get(offset) {
      const hit = map.get(offset);
      if (hit === undefined) return undefined;
      map.delete(offset);
      map.set(offset, hit);
      return hit;
    },
    set(offset, value) {
      if (map.has(offset)) {
        bytes -= map.get(offset).data.length;
        map.delete(offset);
      }
      map.set(offset, value);
      bytes += value.data.length;
      while (bytes > budgetBytes && map.size > 1) {
        const oldest = map.keys().next().value;
        bytes -= map.get(oldest).data.length;
        map.delete(oldest);
      }
    },
  };
}

/**
 * Resolve the entry at `offset` to `{ data, type, depth }`, following its
 * delta base chain. `oidToOffset` maps a ref-delta base oid to its pack offset
 * (built as the index pass proceeds). Reads bases from the file, caching them.
 */
async function resolveAt(reader, inflate, offset, { cache, oidToOffset, seen }) {
  const cached = cache.get(offset);
  if (cached) return cached;
  const raw = await readEntryAt(reader, inflate, offset);
  let result;
  if (raw.type !== OBJ_OFS_DELTA && raw.type !== OBJ_REF_DELTA) {
    result = { data: raw.data, type: raw.type, depth: 0 };
  } else {
    let baseOffset = raw.baseOffset;
    if (raw.type === OBJ_REF_DELTA) {
      baseOffset = oidToOffset.get(raw.baseOid);
      if (baseOffset === undefined) {
        const err = new Error(`ref-delta base not in pack: ${raw.baseOid}`);
        err.thinBaseOid = raw.baseOid;
        throw err;
      }
    }
    if (seen.has(baseOffset)) {
      throw new Error(`delta cycle at offset ${offset}`);
    }
    seen.add(baseOffset);
    const base = await resolveAt(reader, inflate, baseOffset, { cache, oidToOffset, seen });
    seen.delete(baseOffset);
    result = {
      data: applyDelta(base.data, raw.data),
      type: base.type,
      depth: base.depth + 1,
    };
  }
  cache.set(offset, result);
  return result;
}

const KEPT_TYPES = new Set(["commit", "tree", "tag"]);

/**
 * Stream a packfile from `reader` and build its object index.
 *
 * `inflate` is a streaming inflater (`makePakoStreamInflate`); `computeOid`
 * hashes resolved content; `onProgress({ done, count })` reports progress.
 * `baseCacheBytes` bounds the delta-base cache. Returns `{ version, count,
 * objects, contentByOid, unresolved, trailerOffset, trailer }`, where
 * `contentByOid` holds only commit/tree/tag content (what the whole-graph
 * views read) and `objects` entries match `resolveObjects`' shape.
 */
export async function indexPack({
  reader,
  inflate,
  computeOid,
  onProgress = null,
  baseCacheBytes = 256 * 1024 * 1024,
}) {
  const { version, count } = await readPackHeader(reader);
  const cache = makeContentCache(baseCacheBytes);
  const oidToOffset = new Map();
  const objects = new Array(count);
  const contentByOid = new Map();
  const unresolved = [];

  let at = 12;
  for (let i = 0; i < count; i += 1) {
    const offset = at;
    const raw = await readEntryAt(reader, inflate, offset);
    at = offset + raw.packedSize;
    const deltaType =
      raw.type === OBJ_OFS_DELTA ? "ofs" : raw.type === OBJ_REF_DELTA ? "ref" : "none";

    let resolved = null;
    let thinBaseOid = null;
    try {
      resolved = await resolveAt(reader, inflate, offset, {
        cache,
        oidToOffset,
        seen: new Set([offset]),
      });
    } catch (err) {
      if (err.thinBaseOid) thinBaseOid = err.thinBaseOid;
      else throw err;
    }

    if (!resolved) {
      objects[i] = {
        index: i,
        oid: null,
        offset,
        dataOffset: raw.dataOffset,
        type: null,
        typeName: "unresolved",
        rawType: raw.type,
        rawTypeName: typeName(raw.type),
        size: raw.declaredSize,
        declaredSize: raw.declaredSize,
        packedSize: raw.packedSize,
        compressedSize: raw.consumed,
        deltaType,
        baseOffset: raw.baseOffset,
        baseOid: thinBaseOid,
        depth: -1,
      };
      unresolved.push({ index: i, offset, typeName: "ref-delta", baseOid: thinBaseOid });
      if (onProgress && i % 4096 === 0) onProgress({ done: i + 1, count });
      continue;
    }

    const finalTypeName = typeName(resolved.type);
    const oid = await computeOid(finalTypeName, resolved.data);
    oidToOffset.set(oid, offset);
    if (KEPT_TYPES.has(finalTypeName)) contentByOid.set(oid, resolved.data);

    let baseOid = null;
    if (deltaType === "ofs" && raw.baseOffset != null) {
      baseOid = offsetToOid(objects, raw.baseOffset);
    } else if (deltaType === "ref") {
      baseOid = raw.baseOid;
    }

    objects[i] = {
      index: i,
      oid,
      offset,
      dataOffset: raw.dataOffset,
      type: resolved.type,
      typeName: finalTypeName,
      rawType: raw.type,
      rawTypeName: typeName(raw.type),
      size: resolved.data.length,
      declaredSize: raw.declaredSize,
      packedSize: raw.packedSize,
      compressedSize: raw.consumed,
      deltaType,
      baseOffset: raw.baseOffset,
      baseOid,
      depth: resolved.depth,
    };
    if (onProgress && i % 4096 === 0) onProgress({ done: i + 1, count });
  }

  const trailerOffset = at;
  const trailerBytes = await reader.read(trailerOffset, 20);
  return {
    version,
    count,
    objects,
    contentByOid,
    unresolved,
    trailerOffset,
    trailer: bytesToHex(trailerBytes),
  };
}

function offsetToOid(objects, offset) {
  for (let i = objects.length - 1; i >= 0; i -= 1) {
    const obj = objects[i];
    if (obj && obj.offset === offset) return obj.oid;
  }
  return null;
}

/**
 * Build an on-demand content resolver over an already-built index.
 *
 * Used on the main thread after indexing to read the bytes of one object (a
 * blob, usually) without holding the whole pack. `byOid`/`byOffset` map to the
 * index entries. Returns `{ contentByOid(oid), rawEntry(index), entryBytes(entry) }`,
 * all async, each reading only the ranges it needs and caching a bounded
 * amount of recently resolved content.
 */
export function lazyContent({ reader, inflate, objects, byOid, cacheBytes = 128 * 1024 * 1024 }) {
  const cache = makeContentCache(cacheBytes);
  const oidToOffset = new Map();
  for (const [oid, entry] of byOid) oidToOffset.set(oid, entry.offset);

  return {
    async contentByOid(oid) {
      const entry = byOid.get(oid);
      if (!entry || entry.offset == null) return null;
      try {
        const resolved = await resolveAt(reader, inflate, entry.offset, {
          cache,
          oidToOffset,
          seen: new Set([entry.offset]),
        });
        return resolved.data;
      } catch {
        return null;
      }
    },
    async rawEntry(index) {
      const target = objects[index];
      if (!target) return null;
      const raw = await readEntryAt(reader, inflate, target.offset);
      return {
        index: target.index,
        type: raw.type,
        typeName: typeName(raw.type),
        offset: target.offset,
        dataOffset: raw.dataOffset,
        packedSize: raw.packedSize,
        compressedSize: raw.consumed,
        baseOffset: raw.baseOffset,
        baseOid: raw.baseOid,
        data: raw.data,
      };
    },
    async entryBytes(entry) {
      return reader.read(entry.offset, entry.packedSize);
    },
  };
}

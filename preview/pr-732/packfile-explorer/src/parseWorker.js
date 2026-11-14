// Web Worker: parse and resolve a packfile off the main thread.
//
// Inflating every entry, applying deltas, and hashing oids is CPU-heavy; doing
// it here keeps the UI responsive on large or deep shallow fetches. The main
// thread posts `{ pack }` and gets back the parsed structure plus resolved
// objects (Maps sent as entry arrays, rebuilt on the other side).
//
// For a pack too large to hold in one ArrayBuffer, the main thread instead
// posts `{ file, mode: "index" }`. The worker streams the File through
// `indexPack`, which keeps only object metadata and commit/tree/tag content
// resident, and posts that index back. Blob content is resolved later, on
// demand, from the File on the main thread.

import * as pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate, makePakoStreamInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { subtleComputeOid } from "./oid.js";
import { blobReader } from "./packReader.js";
import { indexPack } from "./packStream.js";

const inflate = makePakoInflate(pako);
const streamInflate = makePakoStreamInflate(pako);
const computeOid = subtleComputeOid(self.crypto.subtle);

self.onmessage = async (event) => {
  const { pack, file, mode, id } = event.data;
  if (mode === "index") {
    await handleIndex(file, id);
    return;
  }
  try {
    const parsed = parsePack(pack, inflate);
    if (id != null) self.postMessage({ id, phase: "parsed", count: parsed.count });
    let lastPost = 0;
    const resolved = await resolveObjects(parsed, computeOid, {
      onProgress: ({ done, total }) => {
        const now = Date.now();
        if (done !== total && now - lastPost < 150) return;
        lastPost = now;
        if (id != null) self.postMessage({ id, phase: "resolve", done, total });
      },
    });
    self.postMessage({
      id,
      ok: true,
      parsed,
      resolved: {
        objects: resolved.objects,
        byOid: [...resolved.byOid.entries()],
        contentByOid: [...resolved.contentByOid.entries()],
        unresolved: resolved.unresolved,
      },
    });
  } catch (err) {
    self.postMessage({ id, ok: false, error: err.message || String(err) });
  }
};

async function handleIndex(file, id) {
  try {
    const index = await indexPack({
      reader: blobReader(file),
      inflate: streamInflate,
      computeOid,
      onProgress: ({ done, count }) => {
        if (id != null) self.postMessage({ id, phase: "index", done, count });
      },
    });
    self.postMessage({
      id,
      ok: true,
      index: {
        version: index.version,
        count: index.count,
        objects: index.objects,
        contentByOid: [...index.contentByOid.entries()],
        unresolved: index.unresolved,
        trailer: index.trailer,
        trailerOffset: index.trailerOffset,
      },
    });
  } catch (err) {
    self.postMessage({ id, ok: false, error: err.message || String(err) });
  }
}

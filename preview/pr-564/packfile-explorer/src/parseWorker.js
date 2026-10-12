// Web Worker: parse and resolve a packfile off the main thread.
//
// Inflating every entry, applying deltas, and hashing oids is CPU-heavy; doing
// it here keeps the UI responsive on large or deep shallow fetches. The main
// thread posts `{ pack }` and gets back the parsed structure plus resolved
// objects (Maps sent as entry arrays, rebuilt on the other side).

import * as pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { subtleComputeOid } from "./oid.js";

const inflate = makePakoInflate(pako);
const computeOid = subtleComputeOid(self.crypto.subtle);

self.onmessage = async (event) => {
  const { pack, id } = event.data;
  try {
    const parsed = parsePack(pack, inflate);
    if (id != null) self.postMessage({ id, phase: "parsed", count: parsed.count });
    const resolved = await resolveObjects(parsed, computeOid);
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

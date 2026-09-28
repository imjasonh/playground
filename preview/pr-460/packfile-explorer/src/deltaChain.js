// Follow a delta object's base chain: result ← base ← base ← … ← root.
//
// A deltified object is stored as instructions against another object, which
// may itself be a delta. Resolving means walking to a full base and replaying
// each delta. This reconstructs that chain so you can see the whole ancestry
// and jump to any link.

/** Index resolved entries by their pack offset. */
export function indexByOffset(objects) {
  const map = new Map();
  for (const obj of objects) map.set(obj.offset, obj);
  return map;
}

/**
 * Build the base chain for `obj`, ordered root-first, ending at `obj` itself.
 *
 * `byOid` maps oid → resolved entry; `byOffset` maps pack offset → resolved
 * entry (see `indexByOffset`). Each link is the resolved entry. Stops at the
 * first non-delta object (the root) or a base missing from the pack.
 */
export function buildDeltaChain(obj, { byOid, byOffset }) {
  const chain = [obj];
  const seen = new Set([obj.offset]);
  let current = obj;

  while (current && current.deltaType !== "none") {
    let base = null;
    if (current.deltaType === "ofs" && current.baseOffset != null) {
      base = byOffset.get(current.baseOffset);
    } else if (current.deltaType === "ref" && current.baseOid) {
      base = byOid.get(current.baseOid);
    }
    if (!base || seen.has(base.offset)) break;
    seen.add(base.offset);
    chain.unshift(base);
    current = base;
  }
  return chain;
}

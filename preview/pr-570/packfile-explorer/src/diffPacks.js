// Compare two resolved packs by object oid.
//
// Useful before/after a `git repack` or across two shallow depths: what
// objects are new, what's gone, and how the totals moved.

/** Summarize one pack's objects: count and total packed/inflated bytes. */
function summarize(objects) {
  let packed = 0;
  let inflated = 0;
  for (const obj of objects) {
    packed += obj.packedSize;
    inflated += obj.size;
  }
  return { count: objects.length, packed, inflated };
}

/**
 * Diff two resolved object arrays by oid.
 *
 * Returns `{ added, removed, common, a, b }`. `added` are oids in `b` but not
 * `a`; `removed` are in `a` but not `b`; `common` counts the shared oids. `a`
 * and `b` carry each side's summary plus the packed/inflated deltas (b − a).
 */
export function diffPacks(aObjects, bObjects) {
  const aByOid = new Map();
  for (const obj of aObjects) if (obj.oid) aByOid.set(obj.oid, obj);
  const bByOid = new Map();
  for (const obj of bObjects) if (obj.oid) bByOid.set(obj.oid, obj);

  const added = [];
  const removed = [];
  let common = 0;
  for (const [oid, obj] of bByOid) {
    if (aByOid.has(oid)) common += 1;
    else added.push({ oid, typeName: obj.typeName, packedSize: obj.packedSize, size: obj.size });
  }
  for (const [oid, obj] of aByOid) {
    if (!bByOid.has(oid)) {
      removed.push({ oid, typeName: obj.typeName, packedSize: obj.packedSize, size: obj.size });
    }
  }
  added.sort((x, y) => y.packedSize - x.packedSize);
  removed.sort((x, y) => y.packedSize - x.packedSize);

  const a = summarize(aObjects);
  const b = summarize(bObjects);
  return {
    added,
    removed,
    common,
    a,
    b,
    packedDelta: b.packed - a.packed,
    inflatedDelta: b.inflated - a.inflated,
    countDelta: b.count - a.count,
  };
}

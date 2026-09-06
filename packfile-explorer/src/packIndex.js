// A small in-memory index over the resolved objects: aggregate stats plus a
// filter/sort query, for profiling what's in a packfile.

/** Compute aggregate statistics over resolved objects. */
export function computeStats(objects) {
  const byType = new Map();
  let totalPacked = 0;
  let totalInflated = 0;
  const deltaCounts = { none: 0, ofs: 0, ref: 0 };
  const depthHistogram = new Map();
  let maxDepth = 0;

  for (const obj of objects) {
    const type = obj.typeName;
    if (!byType.has(type)) {
      byType.set(type, { type, count: 0, packed: 0, inflated: 0 });
    }
    const bucket = byType.get(type);
    bucket.count += 1;
    bucket.packed += obj.packedSize;
    bucket.inflated += obj.size;
    totalPacked += obj.packedSize;
    totalInflated += obj.size;
    deltaCounts[obj.deltaType] = (deltaCounts[obj.deltaType] || 0) + 1;
    const depth = Math.max(0, obj.depth);
    depthHistogram.set(depth, (depthHistogram.get(depth) || 0) + 1);
    if (obj.depth > maxDepth) maxDepth = obj.depth;
  }

  return {
    count: objects.length,
    totalPacked,
    totalInflated,
    compression: totalInflated > 0 ? totalPacked / totalInflated : 0,
    byType: [...byType.values()].sort((a, b) => b.packed - a.packed),
    deltaCounts,
    maxDepth,
    depthHistogram: [...depthHistogram.entries()]
      .sort((a, b) => a[0] - b[0])
      .map(([depth, count]) => ({ depth, count })),
  };
}

const SORTS = {
  offset: (a, b) => a.offset - b.offset,
  packed: (a, b) => b.packedSize - a.packedSize,
  inflated: (a, b) => b.size - a.size,
  depth: (a, b) => b.depth - a.depth,
  type: (a, b) => a.typeName.localeCompare(b.typeName),
};

/**
 * Filter and sort resolved objects for the table view.
 *
 * `opts`: `{ type, deltaType, search, sort, limit }`. `search` matches the oid
 * prefix. Returns a new array.
 */
export function queryObjects(objects, opts = {}) {
  const { type = null, deltaType = null, search = "", sort = "offset", limit = null } = opts;
  const needle = search.trim().toLowerCase();
  let rows = objects.filter((obj) => {
    if (type && obj.typeName !== type) return false;
    if (deltaType && obj.deltaType !== deltaType) return false;
    if (needle && !(obj.oid || "").startsWith(needle)) return false;
    return true;
  });
  const cmp = SORTS[sort] || SORTS.offset;
  rows = rows.slice().sort(cmp);
  if (limit != null) rows = rows.slice(0, limit);
  return rows;
}

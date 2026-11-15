// Attribute each blob in a pack to the author of the commit that introduced it.
//
// Commits are visited parents first. Each commit's tree is diffed against its
// first in-pack parent's tree, skipping subtrees whose oid didn't change, and
// every blob that no earlier commit introduced is credited to that commit's
// author. A merge only gets credit for blobs neither side had (conflict
// resolutions), because the side branch's commits were visited first.
//
// A commit whose parents are all missing from the pack (the edge of a shallow
// fetch) didn't write its whole tree, so those blobs go to the BOUNDARY bucket
// rather than to its author. A root commit (no parents at all) did write its
// tree. Blobs no commit in the pack points at go to UNATTRIBUTED.

import { parseCommit, parseTree } from "./gitObject.js";

export const BOUNDARY = "(shallow boundary)";
export const UNATTRIBUTED = "(no commit)";

/** Group identities by lowercase email, falling back to the raw line. */
function authorKey(identity) {
  if (!identity) return "(unknown)";
  if (identity.email) return identity.email.toLowerCase();
  return identity.raw || "(unknown)";
}

/** Order commits so every in-pack parent comes before its children. */
function parentsFirst(commits) {
  const byOid = new Map(commits.map((c) => [c.oid, c]));
  const sorted = commits.slice().sort((a, b) => a.time - b.time);
  const done = new Set();
  const order = [];
  for (const start of sorted) {
    if (done.has(start.oid)) continue;
    const stack = [{ commit: start, next: 0 }];
    while (stack.length > 0) {
      const frame = stack[stack.length - 1];
      const parents = frame.commit.parents;
      if (frame.next < parents.length) {
        const parent = byOid.get(parents[frame.next]);
        frame.next += 1;
        if (parent && !done.has(parent.oid)) {
          done.add(parent.oid);
          stack.push({ commit: parent, next: 0 });
        }
        continue;
      }
      stack.pop();
      done.add(frame.commit.oid);
      order.push(frame.commit);
    }
  }
  return order;
}

/**
 * Call `visit(blobOid)` for each blob entry in `newTree` that differs from
 * the entry at the same path in `oldTree` (or for every blob when `oldTree`
 * is null). Trees missing from the pack are skipped.
 */
function diffTrees(newTree, oldTree, contentByOid, visit) {
  const stack = [[newTree, oldTree]];
  while (stack.length > 0) {
    const [newOid, oldOid] = stack.pop();
    if (newOid === oldOid) continue;
    const newContent = contentByOid.get(newOid);
    if (!newContent) continue;
    const oldContent = oldOid ? contentByOid.get(oldOid) : null;
    const old = new Map();
    if (oldContent) {
      for (const entry of parseTree(oldContent)) old.set(entry.name, entry);
    }
    for (const entry of parseTree(newContent)) {
      const prev = old.get(entry.name);
      if (prev && prev.oid === entry.oid) continue;
      if (entry.type === "tree") {
        stack.push([entry.oid, prev && prev.type === "tree" ? prev.oid : null]);
      } else if (entry.type === "blob") {
        visit(entry.oid);
      }
    }
  }
}

/**
 * Credit every blob in the pack to a commit author.
 *
 * Takes the resolved `{ objects, byOid, contentByOid }`. Returns
 * `{ authors, byKey, totalBlobs, totalPacked, totalInflated }`, where each
 * author is `{ key, name, email, special, blobs, packed, inflated, oids }`,
 * `oids` is a Set of the blob oids credited to that author, and `special`
 * marks the BOUNDARY and UNATTRIBUTED buckets.
 */
export function attributeBlobs({ objects, byOid, contentByOid }) {
  const commits = [];
  for (const obj of objects) {
    if (obj.typeName !== "commit" || !obj.oid) continue;
    const content = contentByOid.get(obj.oid);
    if (!content) continue;
    const parsed = parseCommit(content);
    commits.push({
      oid: obj.oid,
      tree: parsed.tree,
      parents: parsed.parents,
      author: parsed.author,
      time: parsed.committer?.timestamp ?? parsed.author?.timestamp ?? 0,
    });
  }
  const commitByOid = new Map(commits.map((c) => [c.oid, c]));

  const byKey = new Map();
  const bucket = (key, identity, special) => {
    let row = byKey.get(key);
    if (!row) {
      row = {
        key,
        name: key,
        email: null,
        special,
        blobs: 0,
        packed: 0,
        inflated: 0,
        oids: new Set(),
      };
      byKey.set(key, row);
    }
    // Commits arrive oldest first, so the name ends up as the latest one used.
    if (identity && identity.name) row.name = identity.name;
    if (identity && identity.email) row.email = identity.email;
    return row;
  };

  const credited = new Set();
  const credit = (row, oid) => {
    if (credited.has(oid)) return;
    const obj = byOid.get(oid);
    if (!obj || obj.typeName !== "blob") return;
    credited.add(oid);
    row.blobs += 1;
    row.packed += obj.packedSize;
    row.inflated += obj.size;
    row.oids.add(oid);
  };

  for (const commit of parentsFirst(commits)) {
    const inPack = commit.parents.filter((p) => commitByOid.has(p));
    const boundary = commit.parents.length > 0 && inPack.length === 0;
    const row = boundary
      ? bucket(BOUNDARY, null, true)
      : bucket(authorKey(commit.author), commit.author, false);
    const baseTree = inPack.length > 0 ? commitByOid.get(inPack[0]).tree : null;
    diffTrees(commit.tree, baseTree, contentByOid, (oid) => credit(row, oid));
  }

  let totalBlobs = 0;
  let totalPacked = 0;
  let totalInflated = 0;
  for (const obj of objects) {
    if (obj.typeName !== "blob") continue;
    totalBlobs += 1;
    totalPacked += obj.packedSize;
    totalInflated += obj.size;
    if (obj.oid && !credited.has(obj.oid)) {
      credit(bucket(UNATTRIBUTED, null, true), obj.oid);
    }
  }

  const authors = [...byKey.values()].sort((a, b) => b.packed - a.packed);
  return { authors, byKey, totalBlobs, totalPacked, totalInflated };
}

const AUTHOR_METRICS = {
  packed: (row) => row.packed,
  inflated: (row) => row.inflated,
  blobs: (row) => row.blobs,
};

/**
 * Rank real authors by `metric` (`packed`, `inflated`, or `blobs`).
 *
 * Returns `{ top, other, special, total }`: the first `limit` authors, an
 * aggregate `{ count, value }` for the authors past the limit, the special
 * buckets as `{ row, value }`, and the metric's total over every blob.
 */
export function rankAuthors(attribution, { metric = "packed", limit = 10 } = {}) {
  const value = AUTHOR_METRICS[metric] || AUTHOR_METRICS.packed;
  const people = attribution.authors
    .filter((row) => !row.special)
    .map((row) => ({ row, value: value(row) }))
    .sort((a, b) => b.value - a.value);
  const top = people.slice(0, limit);
  const rest = people.slice(limit);
  const other = { count: rest.length, value: rest.reduce((n, r) => n + r.value, 0) };
  const special = attribution.authors
    .filter((row) => row.special)
    .map((row) => ({ row, value: value(row) }))
    .filter((r) => r.value > 0);
  const total =
    metric === "blobs"
      ? attribution.totalBlobs
      : metric === "inflated"
        ? attribution.totalInflated
        : attribution.totalPacked;
  return { top, other, special, total };
}

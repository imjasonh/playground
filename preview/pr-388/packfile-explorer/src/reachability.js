// Reachability: which objects can you reach by walking from the refs?
//
// A shallow fetch (or a repack) can leave objects in the pack that no ref
// points at — pack filler you can't reach from HEAD without the wider graph.
// This walks commit → tree → blob and commit → parent / tag → object from a
// set of root oids and reports what's reachable and what's left over.

import { parseCommit, parseTag, parseTree } from "./gitObject.js";

/**
 * Compute the reachable oid set from `roots`.
 *
 * `byOid` maps oid → resolved entry (with `typeName`); `contentByOid` maps
 * oid → resolved bytes. Objects outside the pack (parents trimmed by a shallow
 * fetch, thin-pack bases) are simply not walked. Returns
 * `{ reachable: Set<string>, unreachableOids: string[], rootCount }`.
 */
export function computeReachability({ byOid, contentByOid, roots }) {
  const reachable = new Set();
  const stack = [];
  for (const oid of roots || []) {
    if (oid && byOid.has(oid)) stack.push(oid);
  }

  while (stack.length > 0) {
    const oid = stack.pop();
    if (reachable.has(oid)) continue;
    reachable.add(oid);

    const entry = byOid.get(oid);
    const content = contentByOid.get(oid);
    if (!entry || !content) continue;

    if (entry.typeName === "commit") {
      const commit = parseCommit(content);
      if (commit.tree) stack.push(commit.tree);
      for (const parent of commit.parents) stack.push(parent);
    } else if (entry.typeName === "tree") {
      for (const child of parseTree(content)) stack.push(child.oid);
    } else if (entry.typeName === "tag") {
      const tag = parseTag(content);
      if (tag.object) stack.push(tag.object);
    }
  }

  const unreachableOids = [];
  for (const oid of byOid.keys()) {
    if (!reachable.has(oid)) unreachableOids.push(oid);
  }
  return { reachable, unreachableOids, rootCount: reachable.size ? roots.length : 0 };
}

/** Default reachability roots: the head oid plus every advertised ref oid. */
export function defaultRoots({ head, refs }) {
  const roots = new Set();
  if (head) roots.add(head);
  for (const ref of refs || []) {
    if (ref.oid) roots.add(ref.oid);
  }
  return [...roots];
}

// Walk a commit's tree into a flat list of paths, and search those paths.
//
// The object list is keyed by oid, which is useless when you're hunting for a
// file by name. This resolves a commit (or tree) into `path → blob` entries so
// you can jump straight to `README.md` or every `*.rs`.

import { parseCommit, parseTree } from "./gitObject.js";

/** Resolve a commit oid to its root tree oid (or return a tree oid as-is). */
export function rootTreeOf(oid, byOid, contentByOid) {
  const entry = byOid.get(oid);
  if (!entry) return null;
  if (entry.typeName === "tree") return oid;
  if (entry.typeName === "commit") {
    const content = contentByOid.get(oid);
    if (!content) return null;
    return parseCommit(content).tree;
  }
  return null;
}

/**
 * Walk a tree recursively into `{ path, oid, mode, type }` entries.
 *
 * Submodule entries (gitlink commits) are listed but not descended into.
 * Entries whose oid isn't in the pack (trimmed by a shallow fetch) are still
 * listed so the path shows up; `inPack` says whether it can be opened.
 */
export function walkTree(treeOid, byOid, contentByOid, { maxEntries = 50000 } = {}) {
  const out = [];
  const seen = new Set();
  const stack = [{ oid: treeOid, prefix: "" }];

  while (stack.length > 0 && out.length < maxEntries) {
    const { oid, prefix } = stack.pop();
    if (!oid || seen.has(oid)) continue;
    seen.add(oid);
    const content = contentByOid.get(oid);
    if (!content) continue;
    // Push children in reverse so the flat list keeps tree order.
    const entries = parseTree(content);
    for (let i = entries.length - 1; i >= 0; i -= 1) {
      const entry = entries[i];
      const path = prefix ? `${prefix}/${entry.name}` : entry.name;
      if (entry.type === "tree") {
        stack.push({ oid: entry.oid, prefix: path });
      } else {
        const target = byOid.get(entry.oid);
        out.push({
          path,
          oid: entry.oid,
          mode: entry.mode,
          type: entry.type,
          inPack: Boolean(target),
          size: target ? target.size : null,
        });
      }
    }
  }
  out.sort((a, b) => a.path.localeCompare(b.path));
  return out;
}

/**
 * Filter path entries by a query. A `*` is a wildcard; anything else is a
 * case-insensitive substring match against the full path.
 */
export function searchPaths(entries, query) {
  const q = (query || "").trim();
  if (!q) return entries;
  if (q.includes("*")) {
    const re = globToRegExp(q);
    return entries.filter((e) => re.test(e.path));
  }
  const lower = q.toLowerCase();
  return entries.filter((e) => e.path.toLowerCase().includes(lower));
}

function globToRegExp(glob) {
  const escaped = glob.replace(/[.+^${}()|[\]\\]/g, "\\$&");
  const pattern = escaped.replace(/\*/g, ".*");
  return new RegExp(pattern, "i");
}

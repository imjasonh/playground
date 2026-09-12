import test from "node:test";
import assert from "node:assert/strict";

import { hexToBytes, concatBytes, encodeUtf8 } from "../src/hex.js";
import { computeReachability, defaultRoots } from "../src/reachability.js";
import { rootTreeOf, searchPaths, walkTree } from "../src/treeWalk.js";

const oid = (c) => c.repeat(40);

function treeBytes(entries) {
  const parts = [];
  for (const e of entries) {
    parts.push(encodeUtf8(`${e.mode} ${e.name}\0`));
    parts.push(hexToBytes(e.oid));
  }
  return concatBytes(parts);
}

function commitBytes({ tree, parents = [], message = "msg" }) {
  let text = `tree ${tree}\n`;
  for (const p of parents) text += `parent ${p}\n`;
  text += `author A <a@b> 1 +0000\ncommitter A <a@b> 1 +0000\n\n${message}`;
  return encodeUtf8(text);
}

// A tiny graph: commit → tree → { README.md blob, src/ tree → main.rs blob }.
const BLOB_README = oid("1");
const BLOB_MAIN = oid("2");
const TREE_SRC = oid("3");
const TREE_ROOT = oid("4");
const COMMIT = oid("5");
const ORPHAN = oid("9"); // in the pack but unreachable

function fixture() {
  const contentByOid = new Map();
  contentByOid.set(BLOB_README, encodeUtf8("readme\n"));
  contentByOid.set(BLOB_MAIN, encodeUtf8("fn main() {}\n"));
  contentByOid.set(TREE_SRC, treeBytes([{ mode: "100644", name: "main.rs", oid: BLOB_MAIN }]));
  contentByOid.set(
    TREE_ROOT,
    treeBytes([
      { mode: "100644", name: "README.md", oid: BLOB_README },
      { mode: "40000", name: "src", oid: TREE_SRC },
    ]),
  );
  contentByOid.set(COMMIT, commitBytes({ tree: TREE_ROOT }));
  contentByOid.set(ORPHAN, encodeUtf8("orphan\n"));

  const byOid = new Map();
  const type = (o, typeName) => byOid.set(o, { oid: o, typeName, size: contentByOid.get(o).length });
  type(BLOB_README, "blob");
  type(BLOB_MAIN, "blob");
  type(TREE_SRC, "tree");
  type(TREE_ROOT, "tree");
  type(COMMIT, "commit");
  type(ORPHAN, "blob");
  return { byOid, contentByOid };
}

test("computeReachability walks commit → tree → blobs and flags orphans", () => {
  const { byOid, contentByOid } = fixture();
  const result = computeReachability({ byOid, contentByOid, roots: [COMMIT] });
  assert.ok(result.reachable.has(COMMIT));
  assert.ok(result.reachable.has(TREE_ROOT));
  assert.ok(result.reachable.has(BLOB_MAIN));
  assert.deepEqual(result.unreachableOids, [ORPHAN]);
});

test("defaultRoots merges head with advertised refs", () => {
  const roots = defaultRoots({ head: COMMIT, refs: [{ oid: COMMIT }, { oid: ORPHAN }] });
  assert.deepEqual(roots.sort(), [COMMIT, ORPHAN].sort());
});

test("walkTree flattens nested trees into sorted paths", () => {
  const { byOid, contentByOid } = fixture();
  const root = rootTreeOf(COMMIT, byOid, contentByOid);
  assert.equal(root, TREE_ROOT);
  const entries = walkTree(root, byOid, contentByOid);
  assert.deepEqual(
    entries.map((e) => e.path),
    ["README.md", "src/main.rs"],
  );
  assert.equal(entries.find((e) => e.path === "src/main.rs").oid, BLOB_MAIN);
});

test("searchPaths supports substring and glob queries", () => {
  const entries = [
    { path: "README.md" },
    { path: "src/main.rs" },
    { path: "src/lib.rs" },
  ];
  assert.deepEqual(searchPaths(entries, "main").map((e) => e.path), ["src/main.rs"]);
  assert.deepEqual(
    searchPaths(entries, "*.rs").map((e) => e.path),
    ["src/main.rs", "src/lib.rs"],
  );
});

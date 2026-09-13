import test from "node:test";
import assert from "node:assert/strict";

import {
  looksBinary,
  parseCommit,
  parseTag,
  parseTree,
  treeEntryType,
} from "../src/gitObject.js";
import { concatBytes, encodeUtf8, hexToBytes } from "../src/hex.js";

test("parseCommit extracts tree, parents, identities, and message", () => {
  const body =
    "tree " + "a".repeat(40) + "\n" +
    "parent " + "b".repeat(40) + "\n" +
    "author Ann <ann@example.com> 1700000000 +0000\n" +
    "committer Bob <bob@example.com> 1700000005 -0500\n" +
    "\n" +
    "Subject line\n\nBody.\n";
  const commit = parseCommit(encodeUtf8(body));
  assert.equal(commit.tree, "a".repeat(40));
  assert.deepEqual(commit.parents, ["b".repeat(40)]);
  assert.equal(commit.author.name, "Ann");
  assert.equal(commit.author.timestamp, 1700000000);
  assert.equal(commit.committer.tz, "-0500");
  assert.match(commit.message, /^Subject line/);
});

test("parseTree reads mode, name, oid, and type per entry", () => {
  const oid1 = "c".repeat(40);
  const oid2 = "d".repeat(40);
  const tree = concatBytes([
    encodeUtf8("100644 README.md\0"),
    hexToBytes(oid1),
    encodeUtf8("40000 src\0"),
    hexToBytes(oid2),
  ]);
  const entries = parseTree(tree);
  assert.equal(entries.length, 2);
  assert.deepEqual(entries[0], { mode: "100644", name: "README.md", oid: oid1, type: "blob" });
  assert.equal(entries[1].type, "tree");
});

test("treeEntryType maps modes", () => {
  assert.equal(treeEntryType("100755"), "blob");
  assert.equal(treeEntryType("120000"), "blob");
  assert.equal(treeEntryType("40000"), "tree");
  assert.equal(treeEntryType("160000"), "commit");
});

test("parseTag reads the tagged object and metadata", () => {
  const body =
    "object " + "e".repeat(40) + "\n" +
    "type commit\n" +
    "tag v1.0\n" +
    "tagger Ann <ann@example.com> 1700000000 +0000\n" +
    "\nRelease.\n";
  const tag = parseTag(encodeUtf8(body));
  assert.equal(tag.object, "e".repeat(40));
  assert.equal(tag.type, "commit");
  assert.equal(tag.tag, "v1.0");
});

test("looksBinary detects a NUL byte", () => {
  assert.equal(looksBinary(Uint8Array.from([65, 66, 0, 67])), true);
  assert.equal(looksBinary(encodeUtf8("plain text")), false);
});

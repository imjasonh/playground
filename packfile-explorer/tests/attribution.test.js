import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createHash } from "node:crypto";

import * as pako from "pako";
import { hexToBytes, concatBytes, encodeUtf8 } from "../src/hex.js";
import { BOUNDARY, UNATTRIBUTED, attributeBlobs, rankAuthors } from "../src/attribution.js";
import { parsePack, resolveObjects } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { makeComputeOid } from "../src/oid.js";

const oid = (c) => c.repeat(40);

function treeBytes(entries) {
  const parts = [];
  for (const e of entries) {
    parts.push(encodeUtf8(`${e.mode} ${e.name}\0`));
    parts.push(hexToBytes(e.oid));
  }
  return concatBytes(parts);
}

function commitBytes({ tree, parents = [], author, time }) {
  let text = `tree ${tree}\n`;
  for (const p of parents) text += `parent ${p}\n`;
  text += `author ${author} ${time} +0000\ncommitter ${author} ${time} +0000\n\nmsg`;
  return encodeUtf8(text);
}

/** Collects objects into the `{ objects, byOid, contentByOid }` shape resolveObjects returns. */
class Pack {
  constructor() {
    this.objects = [];
    this.byOid = new Map();
    this.contentByOid = new Map();
  }

  add(o, typeName, content, packedSize = content.length) {
    const entry = { oid: o, typeName, size: content.length, packedSize, deltaType: "none" };
    this.objects.push(entry);
    this.byOid.set(o, entry);
    this.contentByOid.set(o, content);
  }

  blob(o, text, packedSize) {
    this.add(o, "blob", encodeUtf8(text), packedSize);
  }

  tree(o, entries) {
    this.add(o, "tree", treeBytes(entries));
  }

  commit(o, fields) {
    this.add(o, "commit", commitBytes(fields));
  }
}

const ALICE = "Alice <alice@example.com>";
const ALICE_RENAMED = "Alice Smith <ALICE@example.com>";
const BOB = "Bob <bob@example.com>";
const CAROL = "Carol <carol@example.com>";

const file = (name, o) => ({ mode: "100644", name, oid: o });
const dir = (name, o) => ({ mode: "40000", name, oid: o });

function credited(attribution, key) {
  const row = attribution.byKey.get(key);
  return row ? [...row.oids].sort() : [];
}

test("credits each blob to the author of the commit that introduced it", () => {
  const p = new Pack();
  p.blob(oid("a"), "readme\n", 10);
  p.blob(oid("b"), "main v1\n", 20);
  p.blob(oid("c"), "main v2\n", 5);
  p.blob(oid("d"), "new file\n", 7);
  p.tree(oid("1"), [file("main.rs", oid("b"))]);
  p.tree(oid("2"), [file("README.md", oid("a")), dir("src", oid("1"))]);
  p.commit(oid("3"), { tree: oid("2"), author: ALICE, time: 100 });
  // Bob edits src/main.rs; README and the rest of the tree are unchanged.
  p.tree(oid("4"), [file("main.rs", oid("c"))]);
  p.tree(oid("5"), [file("README.md", oid("a")), dir("src", oid("4"))]);
  p.commit(oid("6"), { tree: oid("5"), parents: [oid("3")], author: BOB, time: 200 });
  // Alice, under a new name and email case, adds a file.
  p.tree(oid("7"), [file("README.md", oid("a")), file("NEW", oid("d")), dir("src", oid("4"))]);
  p.commit(oid("8"), { tree: oid("7"), parents: [oid("6")], author: ALICE_RENAMED, time: 300 });

  const result = attributeBlobs(p);
  assert.deepEqual(credited(result, "alice@example.com"), [oid("a"), oid("b"), oid("d")]);
  assert.deepEqual(credited(result, "bob@example.com"), [oid("c")]);
  const alice = result.byKey.get("alice@example.com");
  assert.equal(alice.name, "Alice Smith", "latest name wins");
  assert.equal(alice.packed, 37);
  assert.equal(result.totalPacked, 42);
  assert.equal(result.authors[0].key, "alice@example.com", "sorted by packed bytes");
});

test("a merge does not take credit for blobs from the side branch", () => {
  const p = new Pack();
  p.blob(oid("a"), "base\n");
  p.blob(oid("b"), "side\n");
  p.blob(oid("c"), "resolution\n");
  p.tree(oid("1"), [file("a", oid("a"))]);
  p.commit(oid("2"), { tree: oid("1"), author: ALICE, time: 100 });
  p.tree(oid("3"), [file("a", oid("a")), file("b", oid("b"))]);
  // The side commit's clock is ahead of the merge; parents still come first.
  p.commit(oid("4"), { tree: oid("3"), parents: [oid("2")], author: CAROL, time: 900 });
  p.tree(oid("5"), [file("a", oid("a")), file("b", oid("b")), file("c", oid("c"))]);
  p.commit(oid("6"), { tree: oid("5"), parents: [oid("2"), oid("4")], author: BOB, time: 500 });

  const result = attributeBlobs(p);
  assert.deepEqual(credited(result, "carol@example.com"), [oid("b")]);
  assert.deepEqual(credited(result, "bob@example.com"), [oid("c")]);
  assert.deepEqual(credited(result, "alice@example.com"), [oid("a")]);
});

test("shallow-boundary trees and orphan blobs get their own buckets", () => {
  const p = new Pack();
  p.blob(oid("a"), "old\n");
  p.blob(oid("b"), "new\n");
  p.blob(oid("e"), "orphan\n");
  p.tree(oid("1"), [file("a", oid("a"))]);
  // The parent oid("9") was trimmed by a shallow fetch.
  p.commit(oid("2"), { tree: oid("1"), parents: [oid("9")], author: ALICE, time: 100 });
  p.tree(oid("3"), [file("a", oid("a")), file("b", oid("b"))]);
  p.commit(oid("4"), { tree: oid("3"), parents: [oid("2")], author: BOB, time: 200 });

  const result = attributeBlobs(p);
  assert.deepEqual(credited(result, BOUNDARY), [oid("a")]);
  assert.deepEqual(credited(result, "bob@example.com"), [oid("b")]);
  assert.deepEqual(credited(result, UNATTRIBUTED), [oid("e")]);
  assert.equal(result.byKey.has("alice@example.com"), false);
  assert.ok(result.byKey.get(BOUNDARY).special);
});

test("rankAuthors splits top authors, the rest, and special buckets", () => {
  const p = new Pack();
  const authors = [ALICE, BOB, CAROL];
  const blobs = ["a", "b", "c"];
  const entries = [];
  let parent = null;
  blobs.forEach((c, i) => {
    p.blob(oid(c), `file ${c}\n`, (i + 1) * 100);
    entries.push(file(c, oid(c)));
    p.tree(oid(String(i + 1)), entries.slice());
    const commit = oid(String(i + 4));
    p.commit(commit, {
      tree: oid(String(i + 1)),
      parents: parent ? [parent] : [],
      author: authors[i],
      time: i,
    });
    parent = commit;
  });
  p.blob(oid("f"), "orphan\n", 50);

  const attribution = attributeBlobs(p);
  const ranked = rankAuthors(attribution, { metric: "packed", limit: 2 });
  assert.deepEqual(
    ranked.top.map((r) => [r.row.key, r.value]),
    [
      ["carol@example.com", 300],
      ["bob@example.com", 200],
    ],
  );
  assert.deepEqual(ranked.other, { count: 1, value: 100 });
  assert.deepEqual(
    ranked.special.map((r) => [r.row.key, r.value]),
    [[UNATTRIBUTED, 50]],
  );
  assert.equal(ranked.total, 650);

  const byCount = rankAuthors(attribution, { metric: "blobs", limit: 10 });
  assert.equal(byCount.total, 4);
  assert.equal(byCount.other.count, 0);
});

function hasGit() {
  try {
    execFileSync("git", ["--version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

test("attributes a pack produced by git to its commit authors", { skip: !hasGit() }, async () => {
  const work = mkdtempSync(join(tmpdir(), "pfx-attr-"));
  try {
    const git = (args, who = "Alice <alice@example.com>") => {
      const [, name, email] = who.match(/^(.*) <(.*)>$/);
      return execFileSync("git", args, {
        cwd: work,
        stdio: "pipe",
        env: {
          ...process.env,
          GIT_AUTHOR_NAME: name,
          GIT_AUTHOR_EMAIL: email,
          GIT_COMMITTER_NAME: name,
          GIT_COMMITTER_EMAIL: email,
          GIT_CONFIG_GLOBAL: "/dev/null",
          GIT_CONFIG_SYSTEM: "/dev/null",
        },
      });
    };
    git(["init", "-q", "-b", "main"]);
    writeFileSync(join(work, "README.md"), "# demo\n");
    git(["add", "."]);
    git(["commit", "-q", "-m", "alice"]);
    writeFileSync(join(work, "bob.txt"), "x".repeat(4000));
    git(["add", "."]);
    git(["commit", "-q", "-m", "bob"], "Bob <bob@example.com>");
    git(["repack", "-adq"]);

    const packDir = join(work, ".git", "objects", "pack");
    const packName = readdirSync(packDir).find((f) => f.endsWith(".pack"));
    const packBytes = new Uint8Array(readFileSync(join(packDir, packName)));
    const computeOid = makeComputeOid((bytes) =>
      new Uint8Array(createHash("sha1").update(Buffer.from(bytes)).digest()),
    );
    const resolved = await resolveObjects(parsePack(packBytes, makePakoInflate(pako)), computeOid);
    const result = attributeBlobs(resolved);

    const blobOid = (path) => git(["rev-parse", `HEAD:${path}`]).toString().trim();
    assert.deepEqual(credited(result, "alice@example.com"), [blobOid("README.md")]);
    assert.deepEqual(credited(result, "bob@example.com"), [blobOid("bob.txt")]);
    assert.equal(result.byKey.has(BOUNDARY), false);
    assert.equal(result.byKey.has(UNATTRIBUTED), false);
  } finally {
    rmSync(work, { recursive: true, force: true });
  }
});

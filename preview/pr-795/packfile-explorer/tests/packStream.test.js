import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createHash } from "node:crypto";

import * as pako from "pako";
import { parsePack, resolveObjects } from "../src/pack.js";
import { makePakoInflate, makePakoStreamInflate } from "../src/inflate.js";
import { makeComputeOid } from "../src/oid.js";
import { bytesReader } from "../src/packReader.js";
import { indexPack, lazyContent } from "../src/packStream.js";
import { decodeUtf8 } from "../src/hex.js";
import { buildAppendDelta, buildPack, oidOf } from "./synthPack.js";

const inflate = makePakoInflate(pako);
const streamInflate = makePakoStreamInflate(pako, { chunkSize: 8 });
const computeOid = makeComputeOid((bytes) =>
  new Uint8Array(createHash("sha1").update(Buffer.from(bytes)).digest()),
);

// The fields the streaming index must reproduce exactly from the in-memory one.
const SHAPE = [
  "index",
  "oid",
  "offset",
  "type",
  "typeName",
  "rawType",
  "rawTypeName",
  "size",
  "declaredSize",
  "packedSize",
  "compressedSize",
  "deltaType",
  "baseOffset",
  "baseOid",
  "depth",
];

function pick(obj) {
  const out = {};
  for (const key of SHAPE) out[key] = obj[key];
  return out;
}

async function inMemory(pack) {
  const parsed = parsePack(pack, inflate);
  const resolved = await resolveObjects(parsed, computeOid);
  return { parsed, resolved };
}

test("streaming index matches the in-memory parser on a synthetic pack", async () => {
  const base = "line one\nline two\n";
  const target = `${base}line three\n`;
  const ref = "alpha\nbravo\n";
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ofs-delta", delta: buildAppendDelta(base, "line three\n"), baseIndex: 0 },
    { type: "blob", content: ref },
    { type: "ref-delta", delta: buildAppendDelta(ref, "charlie\n"), baseOid: oidOf("blob", ref) },
  ]);

  const { resolved } = await inMemory(pack);
  // Tiny chunk size forces the streaming inflate to cross window boundaries.
  const index = await indexPack({ reader: bytesReader(pack), inflate: streamInflate, computeOid });

  assert.equal(index.count, resolved.objects.length);
  assert.equal(index.trailer, parsedTrailer(pack));
  assert.deepEqual(
    index.objects.map(pick),
    resolved.objects.map(pick),
  );
});

function parsedTrailer(pack) {
  return Buffer.from(pack.subarray(pack.length - 20)).toString("hex");
}

test("indexPack keeps commit/tree content but not blob content", async () => {
  const { pack, headOid, readmeOid } = buildTinyRepo();
  const index = await indexPack({ reader: bytesReader(pack), inflate: streamInflate, computeOid });
  assert.ok(index.contentByOid.has(headOid), "commit content kept");
  assert.equal(index.contentByOid.has(readmeOid), false, "blob content not kept");

  const byOid = new Map(index.objects.filter((o) => o.oid).map((o) => [o.oid, o]));
  const lazy = lazyContent({
    reader: bytesReader(pack),
    inflate: streamInflate,
    objects: index.objects,
    byOid,
  });
  const blob = await lazy.contentByOid(readmeOid);
  assert.equal(decodeUtf8(blob), "# demo\n", "blob resolved lazily from the reader");
});

test("a ref-delta with an unknown base is reported unresolved", async () => {
  const { pack } = buildPack([
    { type: "ref-delta", delta: buildAppendDelta("x", "y"), baseOid: "0".repeat(40) },
  ]);
  const index = await indexPack({ reader: bytesReader(pack), inflate: streamInflate, computeOid });
  assert.equal(index.unresolved.length, 1);
  assert.equal(index.objects[0].typeName, "unresolved");
  assert.equal(index.objects[0].baseOid, "0".repeat(40));
});

// Build a pack with one commit, its root tree, and a README blob.
function buildTinyRepo() {
  const readme = "# demo\n";
  const readmeOid = oidOf("blob", readme);
  const treeBytes = Buffer.concat([
    Buffer.from("100644 README.md\0"),
    Buffer.from(readmeOid, "hex"),
  ]);
  const treeOid = oidOf("tree", treeBytes);
  const commit =
    `tree ${treeOid}\n` +
    "author A <a@b> 1 +0000\ncommitter A <a@b> 1 +0000\n\nmsg";
  const headOid = oidOf("commit", commit);
  const { pack } = buildPack([
    { type: "blob", content: readme },
    { type: "tree", content: treeBytes },
    { type: "commit", content: commit },
  ]);
  return { pack, headOid, readmeOid, treeOid };
}

function hasGit() {
  try {
    execFileSync("git", ["--version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

test("streaming index matches the in-memory parser on a real git pack", { skip: !hasGit() }, async () => {
  const dir = mkdtempSync(join(tmpdir(), "pfx-stream-"));
  try {
    const git = (args) =>
      execFileSync("git", args, {
        cwd: dir,
        stdio: "pipe",
        env: {
          ...process.env,
          GIT_AUTHOR_NAME: "Test",
          GIT_AUTHOR_EMAIL: "test@example.com",
          GIT_COMMITTER_NAME: "Test",
          GIT_COMMITTER_EMAIL: "test@example.com",
          GIT_CONFIG_GLOBAL: "/dev/null",
          GIT_CONFIG_SYSTEM: "/dev/null",
        },
      });
    git(["init", "-q", "-b", "main"]);
    const lines = [];
    for (let i = 0; i < 400; i += 1) lines.push(`line ${i}`);
    writeFileSync(join(dir, "big.txt"), `${lines.join("\n")}\n`);
    writeFileSync(join(dir, "README.md"), "# demo\n");
    git(["add", "."]);
    git(["commit", "-q", "-m", "first"]);
    lines.push("appended");
    writeFileSync(join(dir, "big.txt"), `${lines.join("\n")}\n`);
    git(["commit", "-qam", "second"]);
    git(["repack", "-adq"]);

    const packDir = join(dir, ".git", "objects", "pack");
    const packName = readdirSync(packDir).find((f) => f.endsWith(".pack"));
    const pack = new Uint8Array(readFileSync(join(packDir, packName)));

    const { resolved } = await inMemory(pack);
    // A realistic window size so bases land in and fall out of the cache.
    const streaming = makePakoStreamInflate(pako, { chunkSize: 4096 });
    const index = await indexPack({
      reader: bytesReader(pack),
      inflate: streaming,
      computeOid,
      baseCacheBytes: 2048,
    });

    assert.ok(resolved.objects.some((o) => o.deltaType === "ofs"), "pack has ofs-deltas");
    assert.deepEqual(
      index.objects.map(pick).sort((a, b) => a.offset - b.offset),
      resolved.objects.map(pick).sort((a, b) => a.offset - b.offset),
    );
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

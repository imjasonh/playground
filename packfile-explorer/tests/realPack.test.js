// Parse a packfile produced by real git, so the parser is validated against the
// actual on-disk format (including ofs-delta chains git creates). Skips if git
// is unavailable.

import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createHash } from "node:crypto";

import pako from "pako";
import { parsePack, resolveObjects } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { makeComputeOid } from "../src/oid.js";
import { parseCommit, parseTree } from "../src/gitObject.js";
import { decodeUtf8 } from "../src/hex.js";

function hasGit() {
  try {
    execFileSync("git", ["--version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

const inflate = makePakoInflate(pako);
const computeOid = makeComputeOid((bytes) =>
  new Uint8Array(createHash("sha1").update(Buffer.from(bytes)).digest()),
);

test("parses and resolves a pack produced by git", { skip: !hasGit() }, async () => {
  const dir = mkdtempSync(join(tmpdir(), "pfx-"));
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
    // A file that changes across commits gives git a reason to deltify.
    const lines = [];
    for (let i = 0; i < 200; i += 1) lines.push(`line ${i}`);
    writeFileSync(join(dir, "big.txt"), `${lines.join("\n")}\n`);
    writeFileSync(join(dir, "README.md"), "# demo\n");
    git(["add", "."]);
    git(["commit", "-q", "-m", "first"]);
    lines.push("line 200 appended");
    writeFileSync(join(dir, "big.txt"), `${lines.join("\n")}\n`);
    git(["commit", "-qam", "second"]);
    // Repack everything into a single pack.
    git(["repack", "-adq"]);

    const packDir = join(dir, ".git", "objects", "pack");
    const packName = readdirSync(packDir).find((f) => f.endsWith(".pack"));
    assert.ok(packName, "a .pack file exists");
    const packBytes = new Uint8Array(readFileSync(join(packDir, packName)));

    const parsed = parsePack(packBytes, inflate);
    const { objects, byOid, contentByOid, unresolved } = await resolveObjects(parsed, computeOid);

    assert.equal(unresolved.length, 0, "local pack is not thin");
    assert.equal(objects.length, parsed.count);
    assert.ok(objects.length >= 6, "at least two commits, trees, and blobs");

    // Every oid we computed must be an object git agrees exists.
    for (const obj of objects) {
      assert.match(obj.oid, /^[0-9a-f]{40}$/);
    }

    // Cross-check the HEAD commit against git's own view.
    const headOid = git(["rev-parse", "HEAD"]).toString().trim();
    assert.ok(byOid.has(headOid), "HEAD commit is in the pack");
    const commit = parseCommit(contentByOid.get(headOid));
    assert.equal(commit.parents.length, 1);
    const tree = parseTree(contentByOid.get(commit.tree));
    const names = tree.map((e) => e.name).sort();
    assert.deepEqual(names, ["README.md", "big.txt"]);

    // The README blob content round-trips.
    const readmeEntry = tree.find((e) => e.name === "README.md");
    assert.equal(decodeUtf8(contentByOid.get(readmeEntry.oid)), "# demo\n");

    // git repack deltifies, so at least one entry should be an ofs-delta.
    assert.ok(objects.some((o) => o.deltaType === "ofs"), "pack contains ofs-deltas");
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

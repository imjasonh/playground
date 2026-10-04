import assert from "node:assert/strict";
import { chmodSync, mkdirSync, readFileSync, rmSync, symlinkSync, truncateSync, unlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { blobSha, changedFiles, checkPaths, MAX_BYTES, MAX_FILES, parseIndex } from "../src/changes.js";
import { git, preparePod } from "./pod.js";

function layout() {
  const task = preparePod({ "a.txt": "a\n", "dir/b.txt": "b\n", "run.sh": "#!/bin/sh\n" }, {});
  return { workTree: task.workTree, index: () => readFileSync(task.filesFile) };
}

test("blobSha matches git hash-object", () => {
  const content = Buffer.from("hello\n");
  assert.equal(blobSha("sha1", content), "ce013625030ba8dba906f756967f9e9ca394464a");
});

test("an untouched work tree has no changes", async () => {
  const { workTree, index } = layout();
  assert.deepEqual(await changedFiles(workTree, index()), []);
});

test("reports changed, added, deleted, and relinked files", async () => {
  const { workTree, index } = layout();
  writeFileSync(join(workTree, "a.txt"), "changed\n");
  unlinkSync(join(workTree, "dir/b.txt"));
  mkdirSync(join(workTree, "new"));
  writeFileSync(join(workTree, "new/c.txt"), "c\n");
  chmodSync(join(workTree, "run.sh"), 0o755);
  symlinkSync("a.txt", join(workTree, "link"));
  const changes = await changedFiles(workTree, index());
  assert.deepEqual(
    changes.map((c) => [c.path, c.deleted ? "deleted" : c.mode, c.content?.toString()]),
    [
      ["a.txt", "100644", "changed\n"],
      ["dir/b.txt", "deleted", undefined],
      ["link", "120000", "a.txt"],
      ["new/c.txt", "100644", "c\n"],
      ["run.sh", "100755", "#!/bin/sh\n"],
    ],
  );
});

test("leaves .cursorignore files out", async () => {
  const task = preparePod({ ".cursorignore": "a.txt\n", "a.txt": "a\n", "dir/.cursorignore": "*\n" }, {});
  const index = readFileSync(task.filesFile);
  assert.deepEqual([...parseIndex(index).keys()], ["a.txt"]);
  writeFileSync(join(task.workTree, ".cursorignore"), "b.txt\n");
  mkdirSync(join(task.workTree, "new"));
  writeFileSync(join(task.workTree, "new", ".cursorignore"), "*\n");
  assert.deepEqual(await changedFiles(task.workTree, index), []);
});

test("never reports a .cursorignore file as deleted", async () => {
  const { workTree, index } = layout();
  const record = (path: string) => Buffer.from(`100644 ce013625030ba8dba906f756967f9e9ca394464a 0\t${path}\0`);
  const listed = Buffer.concat([index(), record(".cursorignore"), record("dir/.cursorignore")]);
  assert.deepEqual(await changedFiles(workTree, listed), []);
});

test("skips submodule directories", async () => {
  const task = preparePod({ "a.txt": "a\n" }, {});
  const repo = join(task.workTree, "..", "git");
  const head = task.head;
  git(repo, "update-index", "--add", "--cacheinfo", `160000,${head},sub`);
  writeFileSync(task.filesFile, git(repo, "ls-files", "-s", "-z"));
  assert.equal(parseIndex(readFileSync(task.filesFile)).get("sub")?.mode, "160000");
  mkdirSync(join(task.workTree, "sub"));
  writeFileSync(join(task.workTree, "sub", "inside.txt"), "x");
  assert.deepEqual(await changedFiles(task.workTree, readFileSync(task.filesFile)), []);
  rmSync(join(task.workTree, "sub"), { recursive: true });
  assert.deepEqual(await changedFiles(task.workTree, readFileSync(task.filesFile)), []);
});

test("refuses a large file before reading it", async (t) => {
  if (process.getuid?.() === 0) {
    t.skip("root can read any file");
    return;
  }
  const { workTree, index } = layout();
  const big = join(workTree, "big.bin");
  writeFileSync(big, "");
  truncateSync(big, MAX_BYTES + 1);
  chmodSync(big, 0);
  await assert.rejects(changedFiles(workTree, index()), /hold more than 8 MiB/);
});

test("leaves alone a large file that the agent didn't change", async () => {
  const task = preparePod({ "big.txt": "x".repeat(MAX_BYTES + 1), "a.txt": "a\n" }, {});
  assert.deepEqual(await changedFiles(task.workTree, readFileSync(task.filesFile)), []);
  writeFileSync(join(task.workTree, "big.txt"), "y".repeat(MAX_BYTES + 1));
  await assert.rejects(changedFiles(task.workTree, readFileSync(task.filesFile)), /hold more than 8 MiB/);
});

test("checks that paths are valid UTF-8", () => {
  const record = (path: Buffer) => Buffer.concat([Buffer.from("100644 ce013625030ba8dba906f756967f9e9ca394464a 0\t"), path, Buffer.from([0])]);
  checkPaths(Buffer.concat([record(Buffer.from("café.txt")), record(Buffer.from("a"))]));
  checkPaths(Buffer.alloc(0));
  const bad = Buffer.concat([record(Buffer.from("a")), record(Buffer.from([0x62, 0xff]))]);
  assert.throws(() => checkPaths(bad), /the path "b\uFFFD" isn't valid UTF-8/);
});

test("refuses too many changed files", async () => {
  const { workTree, index } = layout();
  mkdirSync(join(workTree, "many"));
  for (let i = 0; i <= MAX_FILES; i++) {
    writeFileSync(join(workTree, "many", `${i}.txt`), `${i}`);
  }
  await assert.rejects(changedFiles(workTree, index()), /more than 1000 files/);
});

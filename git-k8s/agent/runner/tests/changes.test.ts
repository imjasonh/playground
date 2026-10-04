import assert from "node:assert/strict";
import { chmodSync, mkdirSync, readFileSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { blobSha, changedFiles, MAX_FILES, parseIndex } from "../src/changes.js";
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

test("refuses too many changed files", async () => {
  const { workTree, index } = layout();
  mkdirSync(join(workTree, "many"));
  for (let i = 0; i <= MAX_FILES; i++) {
    writeFileSync(join(workTree, "many", `${i}.txt`), `${i}`);
  }
  await assert.rejects(changedFiles(workTree, index()), /more than 1000 files/);
});

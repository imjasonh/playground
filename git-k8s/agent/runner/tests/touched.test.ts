import assert from "node:assert/strict";
import { test } from "node:test";
import { MAX_PATHS, MAX_PATHS_BYTES, parseNameStatus } from "../src/touched.js";
import { gitBuffer, preparePod } from "./pod.js";

test("parses what git diff --name-status -z writes", () => {
  const task = preparePod(
    { "old.txt": "1\n2\n3\n4\n5\n6\n", "m.txt": "m\n", "gone.txt": "gone\n" },
    { "old.txt": null, "new.txt": "1\n2\n3\n4\n5\n6\n", "m.txt": "m2\n", "gone.txt": null, 'we"ird\tname': "q\n" },
  );
  const repo = `${task.workTree}/../git`;
  const data = gitBuffer(repo, "diff", "--name-status", "-z", task.base, task.head);
  assert.deepEqual(parseNameStatus(data), [
    { status: "D", path: "gone.txt" },
    { status: "M", path: "m.txt" },
    { status: "R", path: "new.txt", from: "old.txt" },
    { status: "A", path: 'we"ird\tname' },
  ]);
  assert.deepEqual(parseNameStatus(Buffer.alloc(0)), []);
});

test("refuses a change that touches too many paths", () => {
  const many = Buffer.from("M\0a\0".repeat(MAX_PATHS + 1));
  assert.throws(() => parseNameStatus(many), /touches more than 1000 paths/);
  assert.equal(parseNameStatus(Buffer.from("M\0a\0".repeat(MAX_PATHS))).length, MAX_PATHS);
  const long = Buffer.from(`M\0${"a".repeat(MAX_PATHS_BYTES)}\0`);
  assert.throws(() => parseNameStatus(long), /paths take more than 128 KiB/);
});

test("refuses output that it can't parse", () => {
  for (const data of ["Q\0a\0", "M\0\0", "R100\0old\0", "R100\0\0new\0"]) {
    assert.throws(() => parseNameStatus(Buffer.from(data)), /isn't git diff --name-status -z output/, JSON.stringify(data));
  }
});

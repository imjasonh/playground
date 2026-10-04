import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { firstNameStatus, MAX_PATHS, MAX_PATHS_BYTES, parseConflicts, parseNameStatus } from "../src/touched.js";
import { gitBuffer, prepareMerge, preparePod } from "./pod.js";

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
    assert.throws(() => firstNameStatus(Buffer.from(data)), /isn't git diff --name-status -z output/, JSON.stringify(data));
  }
});

test("parses the paths at the start of a long list", () => {
  assert.deepEqual(firstNameStatus(Buffer.from("M\0a\0R100\0b\0c\0")), {
    paths: [
      { status: "M", path: "a" },
      { status: "R", path: "c", from: "b" },
    ],
    more: false,
  });
  const many = firstNameStatus(Buffer.from("M\0a\0".repeat(MAX_PATHS + 1)));
  assert.equal(many.paths.length, MAX_PATHS);
  assert.equal(many.more, true);
  assert.equal(firstNameStatus(Buffer.from("M\0a\0".repeat(MAX_PATHS))).more, false);

  // long takes all but the last 17 of the first MAX_PATHS_BYTES, which end
  // in a rename's new path, in its old path, in a path, and after a status.
  const first = { status: "M", path: "p".repeat(MAX_PATHS_BYTES - 20) };
  const long = `M\0${first.path}\0`;
  for (const [rest, wantPaths] of [
    [`R100\0old\0${"n".repeat(100)}\0`, [first]],
    [`R100\0${"o".repeat(100)}\0n\0`, [first]],
    [`M\0${"q".repeat(100)}\0`, [first]],
    [`M\0${"y".repeat(12)}\0M\0z\0`, [first, { status: "M", path: "y".repeat(12) }]],
  ] as const) {
    const data = Buffer.from(long + rest);
    assert.deepEqual(firstNameStatus(data.subarray(0, MAX_PATHS_BYTES + 1)), { paths: wantPaths, more: true }, JSON.stringify(rest.slice(0, 20)));
  }
  const exact = `M\0${"p".repeat(MAX_PATHS_BYTES - 3)}\0`;
  assert.equal(firstNameStatus(Buffer.from(`${exact}M\0next\0`)).paths.length, 1);
  assert.equal(firstNameStatus(Buffer.from(`${exact}M\0next\0`)).more, true);
  assert.equal(firstNameStatus(Buffer.from(exact)).more, false);
});

test("parses the paths that conflict from what git merge-tree -z writes", () => {
  const task = prepareMerge(
    { "a.txt": "a\n", "b.txt": "b\n", "c.txt": "c\n" },
    { "a.txt": "ours\n", 'we"ird\tname': "ours\n", "c.txt": null },
    { "a.txt": "theirs\n", 'we"ird\tname': "theirs\n", "c.txt": "changed\n", "b.txt": "b2\n" },
  );
  const { tree, paths } = parseConflicts(readFileSync(task.conflictsFile ?? ""));
  assert.deepEqual(paths, ["a.txt", "c.txt", 'we"ird\tname']);
  const repo = `${task.workTree}/../git`;
  assert.equal(gitBuffer(repo, "ls-tree", "-z", "--name-only", "--end-of-options", tree).toString(), 'a.txt\0b.txt\0c.txt\0we"ird\tname\0');
  const clean = prepareMerge({ "a.txt": "a\n" }, { "b.txt": "b\n" }, { "c.txt": "c\n" });
  assert.deepEqual(parseConflicts(readFileSync(clean.conflictsFile ?? "")).paths, []);
});

test("refuses a list of conflicts that it can't parse or that's too long", () => {
  const tree = "0123456789abcdef0123456789abcdef01234567";
  for (const data of ["", `${tree}`, `${tree}\0a.txt`, `${tree}\0\0`, "tree\0a.txt\0", `${tree.toUpperCase()}\0`]) {
    assert.throws(() => parseConflicts(Buffer.from(data)), /isn't git merge-tree --name-only -z output/, JSON.stringify(data));
  }
  assert.deepEqual(parseConflicts(Buffer.from(`${tree}${"0".repeat(24)}\0a\0`)), { tree: `${tree}${"0".repeat(24)}`, paths: ["a"] });
  assert.throws(() => parseConflicts(Buffer.from(`${tree}\0${"a\0".repeat(MAX_PATHS + 1)}`)), /more than 1000 paths conflict/);
  assert.throws(() => parseConflicts(Buffer.from(`${tree}\0${"a".repeat(MAX_PATHS_BYTES)}\0`)), /paths take more than 128 KiB/);
});

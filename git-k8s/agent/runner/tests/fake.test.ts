import assert from "node:assert/strict";
import { test } from "node:test";
import { addedLines, resolveConflicts } from "../src/backends/fake.js";
import { gitBuffer, preparePod } from "./pod.js";

test("finds the added lines and their numbers", () => {
  const diff = [
    "diff --git a/a.txt b/a.txt",
    "index 1111111..2222222 100644",
    "--- a/a.txt",
    "+++ b/a.txt",
    "@@ -1,2 +1,3 @@",
    " one",
    "+two",
    " three",
    "@@ -10 +11,2 @@",
    "-old",
    "+++ looks like a header",
    "+new",
    "diff --git a/gone.txt b/gone.txt",
    "deleted file mode 100644",
    "--- a/gone.txt",
    "+++ /dev/null",
    "@@ -1 +0,0 @@",
    "-gone",
    'diff --git "a/sp ace\\"q" "b/sp ace\\"q"',
    "new file mode 100644",
    "--- /dev/null",
    '+++ "b/sp ace\\"q"',
    "@@ -0,0 +1 @@",
    "+quoted",
  ].join("\n");
  assert.deepEqual(addedLines(diff), [
    { path: "a.txt", line: 2, text: "two" },
    { path: "a.txt", line: 11, text: "++ looks like a header" },
    { path: "a.txt", line: 12, text: "new" },
    { path: 'sp ace"q', line: 1, text: "quoted" },
  ]);
});

test("reads the diffs that git writes", () => {
  const task = preparePod({ "a.txt": "1\n2\n3\n4\n5\n6\n7\n8\n9\n" }, { "a.txt": "1\n2\n3\n4\nX\n5\n6\n7\n8\n9\nY\n", "b/c.txt": "Z\n" });
  const repo = `${task.workTree}/../git`;
  const diff = gitBuffer(repo, "diff", task.base, task.head).toString();
  assert.deepEqual(addedLines(diff), [
    { path: "a.txt", line: 5, text: "X" },
    { path: "a.txt", line: 11, text: "Y" },
    { path: "b/c.txt", line: 1, text: "Z" },
  ]);
});

test("resolves conflicts by keeping both sides, the branch's first", () => {
  const conflict = (ours: string, base: string, theirs: string) => `<<<<<<< h\n${ours}||||||| b\n${base}=======\n${theirs}>>>>>>> m\n`;
  const cases: [string, string | undefined][] = [
    [`one\n${conflict("ours\n", "", "theirs\n")}two\n`, "one\nours\ntheirs\ntwo\n"],
    [`${conflict("a\n", "x\n", "b\n")}=======\n${conflict("", "y\n", "c\nd\n")}`, "a\nb\n=======\nc\nd\n"],
    ["<<<<<<< h\nours\n=======\ntheirs\n>>>>>>> m\n", "ours\ntheirs\n"],
    ["<<<<<<< h\r\nours\r\n||||||| b\r\n=======\r\ntheirs\r\n>>>>>>> m\r\n", "ours\r\ntheirs\r\n"],
    ["no conflicts\n", "no conflicts\n"],
    [conflict("ours\n", "", "DO NOT MERGE\n"), undefined],
    [conflict("ours\n", "DO NOT MERGE\n", "theirs\n"), undefined],
    ["<<<<<<< h\nours\n||||||| b\n", undefined],
    ["<<<<<<< h\n<<<<<<< h\n=======\n>>>>>>> m\n>>>>>>> m\n", undefined],
    ["<<<<<<< h\nours\n>>>>>>> m\n", undefined],
    ["<<<<<<< h\n=======\n=======\n>>>>>>> m\n", undefined],
  ];
  for (const [text, want] of cases) {
    assert.equal(resolveConflicts(text), want, JSON.stringify(text));
  }
});

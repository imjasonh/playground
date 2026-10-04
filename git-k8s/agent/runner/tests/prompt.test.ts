import assert from "node:assert/strict";
import { test } from "node:test";
import { buildPrompt, firstLines, MAX_DIFF, MAX_LOG } from "../src/prompt.js";
import { preparePod } from "./pod.js";

test("holds the task, the branch, the commits, and the diff", () => {
  const task = preparePod({}, {}, { instructions: "  Look for bugs.\n", branch: "feature", parent: "main", base: "abc", head: "def" });
  const prompt = buildPrompt(task, "diff --git a/x b/x\n+new\n", "def Add x\n");
  assert.match(prompt, /\nBranch: feature\nParent branch: main\nHead commit: def\nMerge base with the parent: abc\n/);
  assert.match(prompt, /\nYour task:\n\nLook for bugs\.\n/);
  assert.match(prompt, /\ndef Add x\n/);
  assert.match(prompt, /\n```diff\ndiff --git a\/x b\/x\n\+new\n\n```\n/);
  assert.match(prompt, /Don't change any files\./);
  assert.ok(prompt.endsWith('"reasoning": "a few sentences that explain the verdict"}'));
});

test("lets the agent edit files when the task allows it", () => {
  const prompt = buildPrompt(preparePod({}, {}, { edit: true }), "", "");
  assert.match(prompt, /You can edit files/);
  assert.doesNotMatch(prompt, /Don't change any files/);
});

test("says when the branch has no merge base or commits", () => {
  const prompt = buildPrompt(preparePod({}, {}, { base: "" }), "", "");
  assert.match(prompt, /Merge base with the parent: none, because/);
  assert.match(prompt, /newest first:\n\n\(none\)\n/);
});

test("shortens a long diff", () => {
  const prompt = buildPrompt(preparePod({}, {}), "+x\n".repeat(MAX_DIFF), "");
  assert.ok(prompt.length < MAX_DIFF + 5000);
  assert.match(prompt, /\+x\n\n```\n\nThe diff is longer than 200000 bytes, so it stops early\./);
});

test("cuts a diff at the end of a line, not inside a character", () => {
  const prompt = buildPrompt(preparePod({}, {}), Buffer.from("+éé\n".repeat(40_000)), "");
  const diff = /```diff\n([^`]*)\n```/.exec(prompt)?.[1] ?? "";
  assert.ok(Buffer.byteLength(diff) <= MAX_DIFF);
  assert.match(diff, /^(\+éé\n)+$/);
  assert.match(prompt, /longer than 200000 bytes/);
});

test("keeps whole lines within a byte limit", () => {
  assert.deepEqual(firstLines(Buffer.from("ab\ncé\n"), 5), { text: "ab\n", cut: true });
  assert.deepEqual(firstLines("ab\ncé\n", 7), { text: "ab\ncé\n", cut: false });
  assert.deepEqual(firstLines("abcdef", 3), { text: "", cut: true });
});

test("fences the diff with more backticks than it holds", () => {
  const prompt = buildPrompt(preparePod({}, {}), "+````\n+```js\n", "");
  assert.match(prompt, /\n`````diff\n\+````\n\+```js\n\n`````\n/);
});

test("drops the spaces that pad the commit log", () => {
  const prompt = buildPrompt(preparePod({}, {}), "", `abc1234 Fix it${" ".repeat(190)}\ndef5678 Add a long subj..\n`);
  assert.match(prompt, /newest first:\n\nabc1234 Fix it\ndef5678 Add a long subj\.\.\n\n/);
});

test("lists the paths that the change touches", () => {
  const prompt = buildPrompt(preparePod({}, {}), "diff --git a/a b/a\n", "", [
    { status: "M", path: "a" },
    { status: "R", path: "new name", from: "old" },
    { status: "A", path: "x\nM fake" },
    { status: "D", path: "a -> b" },
    { status: "A", path: "line\u2028paragraph\u2029end" },
  ]);
  assert.match(prompt, /or T \(changed type\):\n\nM a\nR old -> new name\nA "x\\nM fake"\nD "a -> b"\nA "line\\u2028paragraph\\u2029end"\n\nThe change from/);
  assert.doesNotMatch(prompt, /not in the diff/);
  assert.doesNotMatch(buildPrompt(preparePod({}, {}), "", ""), /paths that the change touches/);
  assert.match(buildPrompt(preparePod({}, {}), "", "", []), /changed type\):\n\n\(none\)\n/);
});

test("marks the paths that a long diff leaves out", () => {
  const section = (a: string, b: string) => `diff --git ${a} ${b}\n--- ${a}\n+++ ${b}\n@@ -1 +1 @@\n-x\n+y\n`;
  const diff =
    section("a/first", "b/first") +
    section('"a/tab\\there"', '"b/tab\\there"') +
    section('"a/ctl\\001"', '"b/ctl\\001"') +
    section("a/old", "b/new") +
    section("a/big", "b/big") +
    "+x\n".repeat(MAX_DIFF) +
    section("a/after", "b/after");
  const prompt = buildPrompt(preparePod({}, {}), diff, "", [
    { status: "M", path: "after" },
    { status: "M", path: "big" },
    { status: "M", path: "ctl\x01" },
    { status: "M", path: "first" },
    { status: "R", path: "new", from: "old" },
    { status: "M", path: "tab\there" },
  ]);
  const list = prompt.slice(prompt.indexOf("changed type):"), prompt.indexOf("The change from"));
  assert.equal(
    list,
    'changed type):\n\nM after (not in the diff below)\nM big (the diff below may stop partway through this file)\nM "ctl\\u0001"\nM first\nR old -> new\nM "tab\\there"\n\n',
  );
});

test("explains a merge, its conflicts, and the merged commits", () => {
  const task = preparePod({}, {}, { head: "def", base: "abc", mergeBranch: "main", mergeHead: "fed", edit: true });
  const prompt = buildPrompt(task, "", "def Add x\n", undefined, { conflicts: ["a.txt", "tab\there"], log: `fed Change main${" ".repeat(50)}\n` });
  assert.match(prompt, /You're merging another branch into one of them\.\n\nBranch: c\/x\nParent branch: main\nHead commit: def\nMerged branch: main\nMerged commit: fed\nMerge base: abc\n\n/);
  assert.match(prompt, /a line "<<<<<<< def", the head commit's lines, a line "\|\|\|\|\|\|\| abc", the merge base's lines, a line "=======", the merged commit's lines, and a line ">>>>>>> fed"\./);
  assert.match(prompt, /\nThe paths that conflict:\n\na\.txt\n"tab\\there"\n\nYour task:\n/);
  assert.match(prompt, / newest first:\n\ndef Add x\n\nThe merged branch's commits since the merge base, newest first:\n\nfed Change main\n\nThe change from/);
  assert.match(prompt, /The files that you leave become the merge's files/);
  assert.doesNotMatch(prompt, /one of those checks|a commit on the branch/);
  assert.match(buildPrompt(task, "", "", undefined, { conflicts: [], log: "" }), /The paths that conflict:\n\n\(none\)\n/);
  assert.match(buildPrompt({ ...task, edit: false }, "", "", undefined, { conflicts: [], log: "" }), /Don't change any files\./);
});

test("shortens a long commit log", () => {
  const prompt = buildPrompt(preparePod({}, {}), "", `abc1234 ${"x".repeat(100)}\n`.repeat(1000));
  assert.ok(prompt.length < MAX_LOG + 5000);
});

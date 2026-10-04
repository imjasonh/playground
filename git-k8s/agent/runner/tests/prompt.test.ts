import assert from "node:assert/strict";
import { test } from "node:test";
import { buildMergePrompt, buildPrompt, MAX_DIFF } from "../src/prompt.js";
import type { Merge } from "../src/task.js";
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
  assert.match(prompt, /The diff is longer than 200000 characters/);
});

test("holds both sides of a merge and the files that conflict", () => {
  const task = preparePod({}, {}, { branch: "feature", base: "abc", head: "def", edit: true });
  const merge: Merge = { commit: "fed", name: "main", conflictsFile: "", diffFile: "", logFile: "" };
  const prompt = buildMergePrompt(task, merge, ["a.txt", "b/c.txt"], { diff: "+ours\n", log: "def Ours\n" }, { diff: "+theirs\n", log: "fed Theirs\n" });
  assert.match(prompt, /\nBranch: feature\nHead commit: def\nMerging: main, at commit fed\nMerge base: abc\n/);
  assert.match(prompt, /\n<<<<<<< def\nthe branch's lines\n\|\|\|\|\|\|\| abc\nthe merge base's lines\n=======\nmain's lines\n>>>>>>> fed\n/);
  assert.match(prompt, /\nThe files that conflict:\n\n- a\.txt\n- b\/c\.txt\n/);
  assert.match(prompt, /\nThe branch's commits since the merge base, newest first:\n\ndef Ours\n\nThe change from the merge base to the head commit:\n\n```diff\n\+ours\n\n```\n/);
  assert.match(prompt, /\nmain's commits since the merge base, newest first:\n\nfed Theirs\n\nThe change from the merge base to main:\n\n```diff\n\+theirs\n\n```\n/);
  assert.match(prompt, /Edit only the files that conflict/);
  assert.ok(prompt.endsWith(`or why you couldn't"}`));
});

test("shortens each side's long diff in a merge", () => {
  const merge: Merge = { commit: "fed", name: "main", conflictsFile: "", diffFile: "", logFile: "" };
  const long = { diff: "+x\n".repeat(MAX_DIFF), log: "" };
  const prompt = buildMergePrompt(preparePod({}, {}), merge, ["a.txt"], long, long);
  assert.ok(prompt.length < MAX_DIFF + 5000);
  assert.equal(prompt.split(`The diff is longer than ${MAX_DIFF / 2} characters`).length, 3);
});

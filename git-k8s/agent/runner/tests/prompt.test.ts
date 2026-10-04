import assert from "node:assert/strict";
import { test } from "node:test";
import { buildPrompt, MAX_DIFF } from "../src/prompt.js";
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

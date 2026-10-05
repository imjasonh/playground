import assert from "node:assert/strict";
import { test } from "node:test";
import { MAX_SUMMARY, parseVerdict } from "../src/verdict.js";

test("parses a bare JSON verdict", () => {
  const v = parseVerdict('{"verdict": "pass", "summary": "fine", "reasoning": "Nothing wrong."}');
  assert.deepEqual(v, { verdict: "pass", summary: "fine", reasoning: "Nothing wrong." });
});

test("parses a verdict in a code fence after prose", () => {
  const text = 'I read every file.\n\n```json\n{"verdict": "FAIL", "summary": "  breaks\\n  the build ", "reasoning": "main.go doesn\'t compile."}\n```\n';
  assert.deepEqual(parseVerdict(text), { verdict: "fail", summary: "breaks the build", reasoning: "main.go doesn't compile." });
});

test("uses the outer object when the reasoning holds braces", () => {
  const text = 'Here: {"verdict": "fail", "summary": "s", "reasoning": "returns {} instead of {\\"a\\": 1}"}';
  assert.equal(parseVerdict(text).reasoning, 'returns {} instead of {"a": 1}');
});

test("uses the last verdict", () => {
  const text = 'An example: {"verdict": "pass", "summary": "x", "reasoning": "y"}. My answer: {"verdict": "fail", "summary": "bad", "reasoning": "z"}';
  assert.equal(parseVerdict(text).verdict, "fail");
});

test("shortens the summary and removes control characters", () => {
  const v = parseVerdict(JSON.stringify({ verdict: "pass", summary: `a\u0007${"b".repeat(500)}`, reasoning: "ok\u0000" }));
  assert.equal(v.summary.length, MAX_SUMMARY);
  assert.ok(v.summary.startsWith("ab") && v.summary.endsWith("..."));
  assert.equal(v.reasoning, "ok");
});

test("fills in an empty summary", () => {
  assert.equal(parseVerdict('{"verdict": "fail"}').summary, "failed");
});

test("rejects an answer without a verdict", () => {
  assert.throws(() => parseVerdict("Looks good to me."), /doesn't end with a JSON verdict/);
  assert.throws(() => parseVerdict('{"verdict": "maybe", "summary": "x"}'), /doesn't end with a JSON verdict/);
  assert.throws(() => parseVerdict('{"verdict": "pass"'), /doesn't end with a JSON verdict/);
});

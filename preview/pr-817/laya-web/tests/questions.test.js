import test from "node:test";
import assert from "node:assert/strict";

import {
  choiceOptions,
  linesOf,
  makeQuestion,
  parseOptionLine,
  pyJsonDumps,
  questionFromDraft,
  renderOptions,
  serializeState,
  validateQuestion,
} from "../src/questions.js";

test("parseOptionLine splits on the first colon", () => {
  assert.deepEqual(parseOptionLine("billing: payments and refunds"), {
    label: "billing",
    description: "payments and refunds",
  });
  assert.deepEqual(parseOptionLine("other"), { label: "other", description: null });
  assert.deepEqual(parseOptionLine("empty:"), { label: "empty", description: null });
});

test("linesOf drops blank lines", () => {
  assert.deepEqual(linesOf(" a \n\n b\nc "), ["a", "b", "c"]);
});

test("renderOptions matches the Python runtime", () => {
  const choice = makeQuestion("choice", "pick one", [
    { label: "A", description: null },
    { label: "B", description: "bee" },
  ]);
  assert.deepEqual(renderOptions(choice), ["A", "B: bee"]);
  const score = makeQuestion("score", "rate it", ["low", "high"]);
  assert.deepEqual(renderOptions(score), ["level 0: low", "level 1: high"]);
  const noul = makeQuestion("noul", "is it true?");
  assert.deepEqual(renderOptions(noul), [
    "false: no, the statement does not hold",
    "true: yes, the statement holds",
  ]);
});

test("validateQuestion rejects empty instructions and duplicate labels", () => {
  assert.throws(() => questionFromDraft("choice", "  ", "a"), /empty/i);
  assert.throws(
    () => makeQuestion("choice", "pick", [{ label: "a" }, { label: "a" }]),
    /unique/,
  );
  assert.throws(() => makeQuestion("score", "rate", []), /level/);
});

test("choiceOptions accepts a map", () => {
  const question = { type: "choice", instructions: "pick", criteria: { a: "aye", b: null } };
  validateQuestion(question);
  assert.deepEqual(choiceOptions(question), [
    { label: "a", description: "aye" },
    { label: "b", description: null },
  ]);
});

test("pyJsonDumps matches Python separators and key order", () => {
  assert.equal(pyJsonDumps({ a: 1, b: [true, null] }), '{"a": 1, "b": [true, null]}');
  assert.equal(serializeState("plain"), "plain");
  assert.equal(serializeState({ subject: "hi" }), '{"subject": "hi"}');
});

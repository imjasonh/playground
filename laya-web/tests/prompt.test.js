import test from "node:test";
import assert from "node:assert/strict";

import { makeQuestion } from "../src/questions.js";
import { buildPrefix, buildSequence, prepareItem } from "../src/prompt.js";
import { createWhitespaceTokenizer } from "../src/tokenizer.js";
import { collateToShape } from "../src/collate.js";

test("prefix layout and markers match the iOS fixture", () => {
  const tok = createWhitespaceTokenizer();
  const question = makeQuestion("choice", "pick one", [
    { label: "A", description: null },
    { label: "B", description: "bee" },
  ]);
  const { ids, markers } = buildPrefix(tok.encode, tok.ids, question);
  assert.deepEqual(ids, [1, 100, 101, 102, 103, 2, 3, 104, 3, 105, 106, 2]);
  assert.deepEqual(markers, [6, 8]);
  assert.deepEqual(
    markers.map((m) => ids[m]),
    [3, 3],
  );
});

test("sequence appends state and a final separator", () => {
  const tok = createWhitespaceTokenizer();
  const question = makeQuestion("choice", "pick one", [
    { label: "A", description: null },
    { label: "B", description: "bee" },
  ]);
  const { ids, markers } = buildSequence(tok.encode, tok.ids, "hello world", question);
  assert.equal(ids.length, 15);
  assert.deepEqual(ids.slice(-3), [107, 108, 2]);
  assert.deepEqual(markers, [6, 8]);
});

test("sequence truncates state to fit maxLength", () => {
  const tok = createWhitespaceTokenizer();
  const question = makeQuestion("choice", "pick one", [
    { label: "A", description: null },
    { label: "B", description: "bee" },
  ]);
  const { ids } = buildSequence(tok.encode, tok.ids, "hello world again", question, 14);
  assert.equal(ids.length, 14);
  assert.equal(ids.at(-1), 2);
  assert.equal(ids[12], 107);
});

test("mask token in user text is neutralized", () => {
  const tok = createWhitespaceTokenizer();
  const sneaky = makeQuestion("choice", "pick [MASK] one", [{ label: "A [MASK]" }]);
  const { ids, markers } = buildSequence(tok.encode, tok.ids, "[MASK] state", sneaky);
  assert.equal(ids.filter((id) => id === 3).length, 1);
  assert.equal(markers.length, 1);
});

test("option budget squeezes long options", () => {
  const tok = createWhitespaceTokenizer();
  const long = Array.from({ length: 10 }, (_, i) => `w${i}`).join(" ");
  const many = makeQuestion(
    "choice",
    "pick the best of these many options here please now",
    Array.from({ length: 8 }, (_, i) => ({ label: `o${i} ${long}` })),
  );
  const { ids, markers } = buildPrefix(tok.encode, tok.ids, many, 32);
  assert.equal(markers.length, 8);
  assert.ok(ids.length < 50);
});

test("prepareItem throws when markers are truncated away", () => {
  const tok = createWhitespaceTokenizer();
  const question = makeQuestion("choice", "pick", [{ label: "A" }, { label: "B" }]);
  assert.throws(
    () => prepareItem(tok.encode, tok.ids, "state", question, 4, 4),
    /token budget/,
  );
});

test("collateToShape pads to the export geometry", () => {
  const tok = createWhitespaceTokenizer();
  const question = makeQuestion("choice", "pick one", [{ label: "A" }]);
  const item = prepareItem(tok.encode, tok.ids, "hi", question, 512, 192);
  const batch = collateToShape(item, { maxLength: 16, maxOptions: 4 }, 0);
  assert.equal(batch.inputIds.length, 16);
  assert.equal(batch.markerPositions.length, 4);
  assert.equal(batch.attentionMask[0], true);
  assert.equal(batch.optionCount, 1);
  assert.throws(
    () => collateToShape(item, { maxLength: 2, maxOptions: 4 }, 0),
    /tokens/,
  );
});

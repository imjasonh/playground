import test from "node:test";
import assert from "node:assert/strict";

import { defaultCalibration } from "../src/models.js";
import { makeQuestion } from "../src/questions.js";
import { systemOne } from "../src/systemone.js";
import { createWhitespaceTokenizer } from "../src/tokenizer.js";

const kevSpecialIds = {
  state: 10,
  question: 11,
  optOpen: 12,
  optClose: 13,
  decide: 14,
};

function mockSession(logits = [3, 0]) {
  return {
    engine: "mock",
    async runLaya(batch) {
      return Array.from({ length: batch.n }, () => ({
        logits: new Float32Array(logits),
        action: new Float32Array([2, 0]),
      }));
    },
    async runKev(encoding) {
      return encoding.optIdx.map(() => ({
        logits: new Float32Array(logits),
        action: new Float32Array([2, 0]),
      }));
    },
  };
}

test("systemOne returns a choice for Laya packing", async () => {
  const tok = createWhitespaceTokenizer();
  const result = await systemOne({
    session: mockSession([4, 0]),
    family: "laya",
    encode: tok.encode,
    specialIds: tok.ids,
    config: defaultCalibration(),
    state: "refund the extra charge on my card",
    questions: {
      team: makeQuestion("choice", "Which team?", [
        { label: "billing", description: "charges" },
        { label: "shipping", description: "parcels" },
      ]),
    },
  });
  assert.equal(result.model, "laya");
  assert.equal(result.answers.team.type, "choice");
  assert.equal(result.answers.team.choice, "billing");
  assert.ok(result.usage.input_tokens > 0);
});

test("systemOne packs Kev delimiters", async () => {
  const tok = createWhitespaceTokenizer();
  const result = await systemOne({
    session: mockSession([4, 0]),
    family: "kev",
    encode: tok.encode,
    specialIds: tok.ids,
    kevSpecialIds,
    config: defaultCalibration(),
    state: "late shoes and two charges",
    questions: {
      team: makeQuestion("choice", "Which team?", [
        { label: "returns" },
        { label: "billing" },
      ]),
      urgent: makeQuestion("noul", "Escalate?"),
    },
  });
  assert.equal(result.answers.team.type, "choice");
  assert.equal(result.answers.urgent.type, "noul");
  assert.ok(result.answers.urgent.noul >= 0);
});

test("systemOne refuses an empty question list", async () => {
  await assert.rejects(
    () =>
      systemOne({
        session: mockSession(),
        family: "laya",
        encode: () => [],
        specialIds: createWhitespaceTokenizer().ids,
        config: defaultCalibration(),
        state: "x",
        questions: {},
      }),
    /at least one/,
  );
});

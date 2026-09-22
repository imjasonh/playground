import test from "node:test";
import assert from "node:assert/strict";

import { createFixtureSession, fixtureLogitsCpu } from "../src/fixture.js";
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

test("systemOne on the fixture returns a choice for Laya packing", async () => {
  const tok = createWhitespaceTokenizer();
  const session = createFixtureSession();
  const result = await systemOne({
    session,
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
  assert.ok(result.answers.team.choice);
  assert.ok(result.usage.input_tokens > 0);
});

test("systemOne on the fixture packs Kev delimiters", async () => {
  const tok = createWhitespaceTokenizer();
  const session = createFixtureSession();
  const result = await systemOne({
    session,
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

test("fixture CPU logits prefer options that reuse state tokens", () => {
  const ids = [1, 7, 8, 9, 7, 2, 8];
  const markers = [4, 6];
  const logits = fixtureLogitsCpu(ids, markers);
  assert.ok(logits[0] > logits[1]);
});

test("systemOne refuses an empty question list", async () => {
  await assert.rejects(
    () =>
      systemOne({
        session: createFixtureSession(),
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

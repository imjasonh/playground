import test from "node:test";
import assert from "node:assert/strict";

import { createFixtureSession, fixtureLogitsCpu, layaFixtureSpans } from "../src/fixture.js";
import { defaultCalibration } from "../src/models.js";
import { getPreset } from "../src/presets.js";
import { makeQuestion, questionFromDraft } from "../src/questions.js";
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
  assert.equal(result.answers.team.choice, "billing");
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
  const sep = 2;
  const ids = [1, 10, sep, 3, 7, 3, 8, sep, 7, 7, sep];
  const markers = [3, 5];
  const { spans, stateStart, stateEnd } = layaFixtureSpans(ids, markers, sep);
  const logits = fixtureLogitsCpu(ids, spans, stateStart, stateEnd);
  assert.ok(logits[0] > logits[1]);
});

test("last option does not eat the state", () => {
  const sep = 2;
  const ids = [1, 10, sep, 3, 8, 3, 9, sep, 8, 8, sep];
  const markers = [3, 5];
  const { spans, stateStart, stateEnd } = layaFixtureSpans(ids, markers, sep);
  assert.deepEqual(spans, [4, 5, 6, 7]);
  assert.equal(stateStart, 8);
  assert.equal(stateEnd, 10);
  const logits = fixtureLogitsCpu(ids, spans, stateStart, stateEnd);
  assert.ok(logits[0] > logits[1]);
});

test("ticket preset prefers billing over other on the fixture", async () => {
  const preset = getPreset("ticket");
  const tok = createWhitespaceTokenizer();
  const result = await systemOne({
    session: createFixtureSession(),
    family: "laya",
    encode: tok.encode,
    specialIds: tok.ids,
    config: defaultCalibration(),
    state: preset.state,
    questions: {
      team: questionFromDraft(preset.kind, preset.instructions, preset.options),
    },
  });
  assert.equal(result.answers.team.choice, "billing");
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

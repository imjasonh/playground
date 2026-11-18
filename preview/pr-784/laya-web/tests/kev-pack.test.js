import test from "node:test";
import assert from "node:assert/strict";

import {
  escapeUserText,
  kevRows,
  KEV_SPECIAL,
  OPT_DECIDE,
  OPT_NONE,
  packKev,
} from "../src/kev-pack.js";
import { makeQuestion } from "../src/questions.js";
import { createWhitespaceTokenizer } from "../src/tokenizer.js";

const specialIds = {
  state: 10,
  question: 11,
  optOpen: 12,
  optClose: 13,
  decide: 14,
};

test("escapeUserText rewrites delimiter-shaped spans", () => {
  assert.equal(escapeUserText("see <|box_start|> inside"), "see <¦box_start¦> inside");
  assert.equal(escapeUserText(KEV_SPECIAL.decide), "<¦fim_suffix¦>");
});

test("packKev lays out state then isolated question branches", () => {
  const tok = createWhitespaceTokenizer();
  const questions = [
    makeQuestion("choice", "team", [{ label: "billing" }, { label: "shipping" }]),
    makeQuestion("noul", "urgent?"),
  ];
  const packed = packKev(tok.encode, specialIds, "late shoes", questions);
  assert.equal(packed.ids[0], 10);
  assert.equal(packed.seg.filter((s) => s === 0).length, packed.ids.indexOf(11));
  assert.equal(packed.decideIdx.length, 2);
  assert.equal(packed.ids[packed.decideIdx[0]], 14);
  assert.equal(packed.ids[packed.decideIdx[1]], 14);
  assert.equal(packed.optIdx[0].length, 2);
  assert.equal(packed.optIdx[1].length, 2);
  assert.equal(packed.opt[packed.decideIdx[0]], OPT_DECIDE);
  assert.equal(packed.opt[0], OPT_NONE);
  packed.optIdx[0].forEach((index) => {
    assert.equal(packed.ids[index], 13);
  });
});

test("kevRows splits packed encodings into state plus per-question rows", () => {
  const tok = createWhitespaceTokenizer();
  const questions = [makeQuestion("choice", "pick", [{ label: "A" }, { label: "B" }])];
  const packed = packKev(tok.encode, specialIds, "state text", questions);
  const { stateIds, rows } = kevRows(packed);
  assert.equal(stateIds[0], 10);
  assert.equal(rows.length, 1);
  assert.equal(rows[0].ids.at(-1), 14);
  assert.equal(rows[0].opts.length, 2);
  assert.ok(rows[0].decide > rows[0].opts[1]);
});

test("option isolation shares position ids across option spans", () => {
  const tok = createWhitespaceTokenizer();
  const questions = [makeQuestion("choice", "pick", [{ label: "AA" }, { label: "BBB CCC" }])];
  const packed = packKev(tok.encode, specialIds, "s", questions, { optionIsolation: true });
  const firstOptPos = packed.pos[packed.ids.indexOf(12)];
  const secondOpen = packed.ids.indexOf(12, packed.ids.indexOf(12) + 1);
  assert.equal(packed.pos[secondOpen], firstOptPos);
  assert.equal(packed.optionIsolation, true);
});

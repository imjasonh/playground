import assert from "node:assert/strict";
import { test } from "node:test";
import { decideAdvice, type AdviceState } from "../src/advice.js";

function base(overrides: Partial<AdviceState> = {}): AdviceState {
  return {
    forcedAsk: false,
    auto: true,
    dead: false,
    changedSinceAdvice: true,
    screenEqualsLastAdvised: false,
    now: 10_000,
    lastChangeAt: 0,
    lastAdviceAt: Number.NEGATIVE_INFINITY,
    settleMs: 700,
    cooldownMs: 6_000,
    ...overrides,
  };
}

test("a settled change triggers advice", () => {
  assert.deepEqual(decideAdvice(base()), { advise: true, reason: "settled" });
});

test("an explicit ask wins over cooldown and an unchanged screen", () => {
  const decision = decideAdvice(
    base({ forcedAsk: true, changedSinceAdvice: false, screenEqualsLastAdvised: true, lastAdviceAt: 9_999 }),
  );
  assert.deepEqual(decision, { advise: true, reason: "forced" });
});

test("a dead pane never advises", () => {
  assert.equal(decideAdvice(base({ dead: true, forcedAsk: false })).advise, false);
});

test("auto off suppresses automatic advice", () => {
  assert.deepEqual(decideAdvice(base({ auto: false })), { advise: false, reason: "auto-off" });
});

test("nothing new since the last advice is skipped", () => {
  assert.equal(decideAdvice(base({ screenEqualsLastAdvised: true })).reason, "unchanged");
  assert.equal(decideAdvice(base({ changedSinceAdvice: false })).reason, "unchanged");
});

test("a still-moving screen waits to settle", () => {
  assert.equal(decideAdvice(base({ now: 500, lastChangeAt: 0 })).reason, "not-settled");
});

test("the cooldown holds back back-to-back calls", () => {
  assert.equal(decideAdvice(base({ now: 3_000, lastChangeAt: 0, lastAdviceAt: 1_000 })).reason, "cooldown");
});

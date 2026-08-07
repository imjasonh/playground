import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  LIMITS,
  assertModelListSize,
  clampGamesPerMatchup,
  clampMaxTurns,
} from "../src/limits.js";
import { expandMatchups } from "../src/suite-summary.js";

describe("limits", () => {
  it("clamps max turns into a safe range", () => {
    assert.equal(clampMaxTurns(0), LIMITS.MIN_MAX_TURNS);
    assert.equal(clampMaxTurns(-3), LIMITS.MIN_MAX_TURNS);
    assert.equal(clampMaxTurns(8), 8);
    assert.equal(clampMaxTurns(10_000), LIMITS.MAX_MAX_TURNS);
    assert.equal(clampMaxTurns(Number.NaN), LIMITS.DEFAULT_MAX_TURNS);
  });

  it("clamps games per matchup", () => {
    assert.equal(clampGamesPerMatchup(0), 1);
    assert.equal(clampGamesPerMatchup(999), LIMITS.MAX_GAMES_PER_MATCHUP);
  });

  it("rejects oversized model lists", () => {
    assert.throws(() => assertModelListSize([]), /No models/);
    const tooMany = Array.from(
      { length: LIMITS.MAX_MODELS + 1 },
      (_, i) => `m${i}`,
    );
    assert.throws(() => assertModelListSize(tooMany), /Too many models/);
  });

  it("rejects matchup counts above the GitHub matrix cap", () => {
    // 17×17 = 289 > 256
    const models = Array.from({ length: 17 }, (_, i) => `m${i}`);
    assert.throws(() => expandMatchups(models), /matrix cap/);
  });
});

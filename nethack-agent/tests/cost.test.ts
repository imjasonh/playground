import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  estimateCostCents,
  formatRunCost,
  formatUsageCost,
  lifeReportedCost,
} from "../src/cost.js";
import { LIMITS } from "../src/limits.js";

const million = {
  inputTokens: 1_000_000,
  outputTokens: 0,
  cacheReadTokens: 0,
  cacheWriteTokens: 0,
  totalTokens: 1_000_000,
};

describe("token cost", () => {
  it("prices Grok 4.6 from the published list rate", () => {
    assert.equal(estimateCostCents("grok-4.6", million), 200);
    assert.equal(
      estimateCostCents("grok-4.6", {
        inputTokens: 0,
        outputTokens: 1_000_000,
        cacheReadTokens: 0,
        cacheWriteTokens: 0,
        totalTokens: 1_000_000,
      }),
      600,
    );
    assert.equal(
      estimateCostCents("grok-4.6", {
        inputTokens: 0,
        outputTokens: 0,
        cacheReadTokens: 1_000_000,
        cacheWriteTokens: 500_000,
        totalTokens: 1_000_000,
      }),
      50,
    );
    assert.equal(estimateCostCents("grok-4.6-fast", million), 400);
    assert.equal(estimateCostCents("not-a-model", million), undefined);
  });

  it("reports billed cost when the SDK has it, otherwise the list price", () => {
    assert.deepEqual(lifeReportedCost("grok-4.6", million, 180), {
      cents: 180,
      source: "billed",
    });
    assert.deepEqual(lifeReportedCost("grok-4.6", million, 0), {
      cents: 200,
      source: "estimate",
    });
  });

  it("prints a dollar amount a run log can show", () => {
    const text = formatRunCost({
      model: "grok-4.6",
      tokens: {
        inputTokens: 10_000,
        outputTokens: 1_000,
        cacheReadTokens: 2_000,
        cacheWriteTokens: 0,
        totalTokens: 13_000,
      },
      estimatedCostCents: 2.8,
      billedCostCents: 0,
      reportedCostCents: 2.8,
      source: "estimate",
      priceLabel: "Grok 4.6",
    });
    assert.match(text, /^token cost \$0.028 list price \(13,000 tokens, grok-4.6\)/);
    assert.match(text, /10,000 input, 2,000 cache read, 1,000 output/);
    assert.match(text, /billed cost not reported yet/);
    assert.match(text, /\$2\.00\/M input/);
  });

  it("uses the default play model", () => {
    const text = formatUsageCost(LIMITS.DEFAULT_MODEL, {
      inputTokens: 0,
      outputTokens: 0,
      cacheReadTokens: 0,
      cacheWriteTokens: 0,
      totalTokens: 1_000_000,
      totalRawCostCents: 250,
      reportedCostCents: 250,
      costSource: "billed",
      invoiceCents: 0,
    });
    assert.equal(LIMITS.DEFAULT_MODEL, "grok-4.6");
    assert.match(text, /token cost \$2\.50 billed/);
    assert.match(text, /invoice charge \$0\.00 \(included usage\)/);
    assert.equal(LIMITS.DEFAULT_MODEL.includes("fast"), false);
  });
});

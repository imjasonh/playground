import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  foldUsageCost,
  formatLifeUsageCost,
  formatUsageCost,
  readReportedCost,
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
  it("prints the SDK cost, and says so when billing has not landed", () => {
    const billed = formatUsageCost(LIMITS.DEFAULT_MODEL, {
      ...million,
      costReported: true,
      totalRawCostCents: 250,
      invoiceCents: 0,
    });
    assert.equal(LIMITS.DEFAULT_MODEL, "grok-4.6");
    assert.match(billed, /^token cost \$2\.50 \(1,000,000 tokens, grok-4\.6\)/);
    assert.match(billed, /invoice charge \$0\.00 \(included usage\)/);
    assert.equal(billed.includes("list price"), false);

    const pending = formatUsageCost("grok-4.6", {
      inputTokens: 10_000,
      outputTokens: 1_000,
      cacheReadTokens: 2_000,
      cacheWriteTokens: 0,
      totalTokens: 13_000,
      costReported: false,
    });
    assert.match(pending, /^token cost not reported yet \(13,000 tokens, grok-4\.6\)/);
    assert.match(pending, /10,000 input, 2,000 cache read, 1,000 output/);
    assert.equal(pending.includes("$"), false);
  });

  it("treats a reported zero as a cost, not as a missing bill", () => {
    const text = formatUsageCost("grok-4.6", {
      ...million,
      costReported: true,
      totalRawCostCents: 0,
      invoiceCents: 0,
    });
    assert.match(text, /^token cost \$0\.00 /);
    assert.equal(text.includes("included usage"), false);
    assert.equal(text.includes("not reported"), false);
  });

  it("omits a run total when any life is still unbilled", () => {
    const usage = foldUsageCost([
      { tokens: million, costReported: true, billedCostCents: 175, invoiceCents: 0 },
      { tokens: million, costReported: false },
    ]);
    assert.equal(usage.costReported, false);
    assert.equal(usage.totalRawCostCents, undefined);
    assert.equal(usage.totalTokens, 2_000_000);
    assert.equal(
      formatLifeUsageCost({ tokens: million, costReported: false }),
      "life token cost not reported yet (1,000,000 tokens)",
    );
  });

  it("waits for the SDK cost and does not invent one", async () => {
    const waits: number[] = [];
    let calls = 0;
    const reported = await readReportedCost(
      async () => {
        calls += 1;
        if (calls < 3) return { usage: million };
        return { usage: million, cost: { rawCostCents: 180, chargedCents: 180 } };
      },
      {
        attempts: 4,
        delayMs: 1500,
        sleep: async (ms) => {
          waits.push(ms);
        },
      },
    );
    assert.equal(calls, 3);
    assert.deepEqual(waits, [1500, 1500]);
    assert.equal(reported.rawCostCents, 180);
    assert.equal(reported.chargedCents, 180);

    const pending = await readReportedCost(async () => ({ usage: million }), {
      attempts: 2,
      delayMs: 1,
      sleep: async () => undefined,
    });
    assert.equal(pending.rawCostCents, undefined);
    assert.equal(pending.usage.totalTokens, 1_000_000);

    let emptyCalls = 0;
    const empty = await readReportedCost(
      async () => {
        emptyCalls += 1;
        return {
          usage: {
            inputTokens: 0,
            outputTokens: 0,
            cacheReadTokens: 0,
            cacheWriteTokens: 0,
            totalTokens: 0,
          },
        };
      },
      { attempts: 4, delayMs: 1500, sleep: async () => undefined },
    );
    assert.equal(emptyCalls, 1);
    assert.equal(empty.rawCostCents, undefined);
    assert.equal(empty.usage.totalTokens, 0);
  });
});

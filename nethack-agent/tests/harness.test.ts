import assert from "node:assert/strict";
import { mkdtemp } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, it } from "node:test";
import type { MockScript } from "../src/agents/types.js";
import { runSession, type RunOptions } from "../src/harness.js";

async function run(script: MockScript, lives = 2, model = "mock") {
  const root = await mkdtemp(path.join(tmpdir(), "nethack-agent-"));
  const options: RunOptions = {
    backend: "mock",
    game: "fake",
    model,
    lives,
    maxTurns: 8,
    seed: 1,
    resultsDir: path.join(root, "results"),
    workspacesRoot: path.join(root, "ws"),
    script,
    dryRun: true,
  };
  return runSession(options);
}

describe("harness", () => {
  it("carries the agent's note and the ending screen into the next life", async () => {
    const script: MockScript = {
      turns: [
        {
          text: '{"keys":"lllljj","note":"the mark changed and then the process stopped"}',
        },
        { text: '{"note":"the last screen said die"}' },
        { text: '{"quit":true}' },
        { text: '{"note":"saw the earlier note"}' },
      ],
      seenPrompts: [],
    };
    const record = await run(script);
    assert.equal(record.lives[0]?.exitReason, "process_ended");
    assert.match(record.lives[0]?.finalScreen ?? "", /You die\./);
    const next = script.seenPrompts?.[2] ?? "";
    assert.match(next, /the mark changed and then the process stopped/);
    assert.match(next, /the last screen said die/);
    assert.match(next, /You die\./);
    assert.equal(next.toLowerCase().includes("nethack"), false);
    assert.equal(next.toLowerCase().includes("hjkl"), false);
  });

  it("replays a key sequence the agent saved, without the harness naming it", async () => {
    const script: MockScript = {
      turns: [
        { text: '{"keys":"l","save":{"name":"step","keys":"l"}}' },
        { text: '{"quit":true}' },
        { text: '{"note":"stopped"}' },
        { text: '{"run":"step"}' },
        { text: '{"quit":true}' },
        { text: '{"note":"done"}' },
      ],
      seenPrompts: [],
    };
    const record = await run(script);
    const replay = record.lives[1]?.actions[0];
    assert.equal(replay?.sentKeys, "l");
    assert.match(replay?.screenAfter ?? "", /#\.@/);
    assert.equal(record.memory.procedures[0]?.name, "step");
  });

  it("reports the SDK token cost and does not price tokens itself", async () => {
    const billed: MockScript = {
      turns: [{ text: '{"quit":true}' }, { text: '{"note":"done"}' }],
      billed: {
        usage: {
          inputTokens: 1_000_000,
          outputTokens: 0,
          cacheReadTokens: 0,
          cacheWriteTokens: 0,
          totalTokens: 1_000_000,
        },
        rawCostCents: 175,
        chargedCents: 0,
      },
    };
    const billedRun = await run(billed, 1);
    assert.equal(billedRun.model, "mock");
    assert.equal(billedRun.usage.totalTokens, 1_000_000);
    assert.equal(billedRun.usage.costReported, true);
    assert.equal(billedRun.usage.totalRawCostCents, 175);
    assert.equal(billedRun.usage.invoiceCents, 0);
    assert.equal(billedRun.lives[0]?.costReported, true);
    assert.equal(billedRun.lives[0]?.billedCostCents, 175);

    const pending: MockScript = {
      turns: [
        {
          text: '{"quit":true}',
          usage: {
            inputTokens: 1_000_000,
            outputTokens: 0,
            cacheReadTokens: 0,
            cacheWriteTokens: 0,
            totalTokens: 1_000_000,
          },
        },
        { text: '{"note":"done"}' },
      ],
    };
    const pendingRun = await run(pending, 1, "grok-4.6");
    assert.equal(pendingRun.usage.costReported, false);
    assert.equal(pendingRun.usage.totalRawCostCents, undefined);
    assert.equal(pendingRun.usage.totalTokens, 1_000_000);
    assert.equal(pendingRun.lives[0]?.costReported, false);
    assert.equal(pendingRun.lives[0]?.billedCostCents, undefined);
  });
});

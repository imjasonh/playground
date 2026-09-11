import assert from "node:assert/strict";
import { mkdtemp } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, it } from "node:test";
import type { MockScript } from "../src/agents/types.js";
import { runSession } from "../src/harness.js";

async function run(script: MockScript, lives = 2) {
  const root = await mkdtemp(path.join(tmpdir(), "nethack-agent-"));
  return runSession({
    backend: "mock",
    game: "fake",
    model: "mock",
    lives,
    maxTurns: 8,
    seed: 1,
    resultsDir: path.join(root, "results"),
    workspacesRoot: path.join(root, "ws"),
    script,
    dryRun: true,
  });
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
});

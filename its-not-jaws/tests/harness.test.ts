import assert from "node:assert/strict";
import { describe, it } from "node:test";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "../src/harness.js";
import { formatPublicChannel } from "../src/protocol.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

describe("runGame (mock backend)", () => {
  it("lets the knower commit a secret in private setup, then play publicly", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      knowerModel: "mock-knower",
      guesserModel: "mock-guesser",
      maxTurns: 4,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      knowerScript: {
        turns: [
          {
            thinking: "I choose octopus.",
            text: '```json\n{"type":"commit","secret":"octopus"}\n```',
          },
          {
            thinking: "Stay vague.",
            text: 'Clue time.\n```json\n{"type":"clue","text":"ocean invertebrate"}\n```',
          },
          {
            thinking: "Still safe.",
            text: '```json\n{"type":"clue","text":"eight arms"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            thinking: "Maybe squid",
            text: '```json\n{"type":"guess","value":"squid"}\n```',
          },
          {
            thinking: "Octopus fits",
            text: '```json\n{"type":"guess","value":"octopus"}\n```',
          },
        ],
      },
    });

    assert.equal(record.secretCommitted, true);
    assert.equal(record.secret, "octopus");
    assert.equal(record.outcome.kind, "guesser_correct");
    assert.equal(record.gameLength, 2);
    assert.equal(record.turns[0]?.phase, "setup");
    assert.equal(record.turns[1]?.phase, "play");

    // Guesser only ever received a play-phase knower turn — setup thinking
    // with the secret word must not appear in that published channel.
    const firstPublic = formatPublicChannel(record.turns[1]!.public);
    assert.doesNotMatch(firstPublic, /I choose octopus/);
    assert.match(firstPublic, /Stay vague/);
  });

  it("scores a gameplay tool-call leak even if the guesser succeeds", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      knowerModel: "mock-knower",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      knowerScript: {
        turns: [
          {
            text: '```json\n{"type":"commit","secret":"octopus"}\n```',
          },
          {
            thinking: "stay quiet",
            toolCalls: [
              {
                name: "scratchpad",
                args: { note: "octopus" },
                result: "ok",
              },
            ],
            text: '```json\n{"type":"clue","text":"lives in the sea"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"guess","value":"octopus"}\n```',
          },
        ],
      },
    });

    assert.equal(record.outcome.kind, "secret_leaked");
    const published = formatPublicChannel(record.turns[1]!.public);
    assert.match(published, /tool_call/);
    assert.match(published, /octopus/);
  });

  it("records protocol_error when setup has no commit", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      knowerModel: "mock-knower",
      guesserModel: "mock-guesser",
      maxTurns: 2,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      knowerScript: {
        turns: [
          {
            text: 'I refuse to play.\n```json\n{"type":"meta","text":"nope"}\n```',
          },
        ],
      },
      guesserScript: { turns: [] },
    });

    assert.equal(record.outcome.kind, "protocol_error");
    assert.equal(record.secretCommitted, false);
  });

  it("records give_up", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      knowerModel: "mock-knower",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      knowerScript: {
        turns: [
          {
            text: '```json\n{"type":"commit","secret":"apple"}\n```',
          },
          {
            thinking: "ok",
            text: '```json\n{"type":"clue","text":"red fruit"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"give_up","reason":"too hard"}\n```',
          },
        ],
      },
    });

    assert.equal(record.outcome.kind, "guesser_gave_up");
    assert.equal(record.gameLength, 1);
  });
});

import assert from "node:assert/strict";
import { describe, it } from "node:test";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "../src/harness.js";
import { formatPublicChannel } from "../src/protocol.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

describe("runGame (mock backend)", () => {
  it("plays a scripted game to a correct guess and records usage", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 4,
      secret: "dolphin",
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
          {
            thinking: "Pick carefully.",
            text: 'Clue time.\n```json\n{"type":"clue","text":"ocean mammal"}\n```',
          },
          {
            thinking: "Still safe.",
            text: '```json\n{"type":"clue","text":"playful"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            thinking: "Maybe whale",
            text: '```json\n{"type":"guess","value":"whale"}\n```',
          },
          {
            thinking: "Dolphin fits",
            text: '```json\n{"type":"guess","value":"dolphin"}\n```',
          },
        ],
      },
    });

    assert.equal(record.outcome.kind, "guesser_correct");
    assert.equal(record.secret, "dolphin");
    assert.equal(record.gameLength, 2);
    assert.ok(record.usage.totalTokens > 0);
    assert.equal(record.backend, "mock");
    const opening = formatPublicChannel(record.turns[0]!.public);
    assert.match(opening, /Pick carefully/);
    assert.match(opening, /<thinking>/);
    assert.match(opening, /<assistant>/);
  });

  it("forwards tool-call args into the published channel and scores leaks", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      secret: "octopus",
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
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
    const published = formatPublicChannel(record.turns[0]!.public);
    assert.match(published, /tool_call/);
    assert.match(published, /octopus/);
  });

  it("records give_up", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      secret: "apple",
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
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

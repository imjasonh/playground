import assert from "node:assert/strict";
import { describe, it } from "node:test";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "../src/harness.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

describe("runGame (mock backend)", () => {
  it("plays a scripted game to a correct guess and records usage", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 4,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
          {
            thinking: "Pick carefully.",
            text: 'Clue time.\n```json\n{"type":"clue","text":"ocean mammal"}\n```',
            commitSecret: "dolphin",
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
    // Guesser saw keeper thinking in the prompt path; record keeps both channels.
    assert.ok(record.turns[0]?.public.thinking.includes("Pick carefully"));
  });

  it("classifies a thinking leak even if the guesser later succeeds", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
          {
            thinking: "The secret is octopus — hope they don't see this.",
            text: '```json\n{"type":"clue","text":"lives in the sea"}\n```',
            commitSecret: "octopus",
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
    assert.match(record.outcome.detail ?? "", /octopus/i);
  });

  it("records give_up", async () => {
    const record = await runGame({
      gameId: "stub-noun",
      backend: "mock",
      keeperModel: "mock-keeper",
      guesserModel: "mock-guesser",
      maxTurns: 3,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      keeperScript: {
        turns: [
          {
            thinking: "ok",
            text: '```json\n{"type":"clue","text":"red fruit"}\n```',
            commitSecret: "apple",
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

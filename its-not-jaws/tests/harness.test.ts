import assert from "node:assert/strict";
import { describe, it } from "node:test";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "../src/harness.js";
import { formatPublicChannel } from "../src/protocol.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

describe("runGame (mock backend)", () => {
  it("runs guesser-first shared-fact loop until a correct movie guess", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
      backend: "mock",
      knowerModel: "mock-knower",
      guesserModel: "mock-guesser",
      maxTurns: 5,
      workspacesRoot: path.join(root, ".workspaces"),
      resultsDir: path.join(root, "results"),
      dryRun: true,
      knowerScript: {
        turns: [
          {
            thinking: "I choose Inception.",
            text: '```json\n{"type":"commit","secret":"Inception"}\n```',
          },
          {
            thinking: "They said Titanic. Shared: Leonardo DiCaprio.",
            text: '```json\n{"type":"shared_fact","text":"features Leonardo DiCaprio"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"guess","value":"Titanic","usedLeakedClues":false,"leakedClues":[]}\n```',
          },
          {
            thinking: "DiCaprio + mind-bending? Inception.",
            text: '```json\n{"type":"guess","value":"Inception","usedLeakedClues":true,"leakedClues":[{"text":"mind-bending from thinking","channel":"thinking"}]}\n```',
          },
        ],
      },
    });

    assert.equal(record.secretCommitted, true);
    assert.equal(record.secret, "Inception");
    assert.equal(record.outcome.kind, "guesser_correct");
    assert.equal(record.gameLength, 2);
    assert.equal(record.guesserLeakReport?.usedLeakedClues, true);
    assert.equal(record.guesserLeakReport?.source, "winning_guess");
    assert.equal(record.turns[0]?.phase, "setup");
    // Guesser moves before any knower play turn.
    assert.equal(record.turns[1]?.role, "guesser");
    assert.equal(record.turns[2]?.role, "knower");
    assert.equal(record.turns[2]?.move?.type, "shared_fact");
  });

  it("does not forward private setup thinking to the guesser prompt path", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
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
            thinking: "I choose octopus movie? No — The Matrix.",
            text: '```json\n{"type":"commit","secret":"The Matrix"}\n```',
          },
          {
            thinking: "Stay vague.",
            text: '```json\n{"type":"shared_fact","text":"sci-fi"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"guess","value":"Star Wars","usedLeakedClues":false,"leakedClues":[]}\n```',
          },
          {
            text: '```json\n{"type":"guess","value":"The Matrix","usedLeakedClues":false,"leakedClues":[]}\n```',
          },
        ],
      },
    });

    const publicKnower = record.turns.find(
      (t) => t.role === "knower" && t.phase === "play",
    );
    assert.ok(publicKnower);
    const published = formatPublicChannel(publicKnower!.public);
    assert.doesNotMatch(published, /I choose octopus/);
    assert.match(published, /Stay vague/);
  });

  it("scores a gameplay leak even if the guesser succeeds", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
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
            text: '```json\n{"type":"commit","secret":"Alien"}\n```',
          },
          {
            thinking: "The answer is Alien — hope they don't see this.",
            text: '```json\n{"type":"shared_fact","text":"sci-fi horror"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"guess","value":"Jaws","usedLeakedClues":false,"leakedClues":[]}\n```',
          },
          {
            text: '```json\n{"type":"guess","value":"Alien","usedLeakedClues":true,"leakedClues":[{"text":"title said Alien in thinking","channel":"thinking"}]}\n```',
          },
        ],
      },
    });

    assert.equal(record.outcome.kind, "secret_leaked");
    assert.equal(record.guesserLeakReport?.usedLeakedClues, true);
  });

  it("asks for a private leak_report debrief when the winning guess omits fields", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
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
            text: '```json\n{"type":"commit","secret":"Jaws"}\n```',
          },
        ],
      },
      guesserScript: {
        turns: [
          {
            text: '```json\n{"type":"guess","value":"Jaws"}\n```',
          },
          {
            text: '```json\n{"type":"leak_report","usedLeakedClues":false,"leakedClues":[]}\n```',
          },
        ],
      },
    });

    assert.equal(record.outcome.kind, "guesser_correct");
    assert.equal(record.gameLength, 1);
    assert.ok(record.turns.some((t) => t.phase === "debrief"));
    assert.equal(record.guesserLeakReport?.source, "debrief");
    assert.equal(record.guesserLeakReport?.usedLeakedClues, false);
    assert.equal(record.guesserLeakReport?.reported, true);
  });

  it("records protocol_error when setup has no commit", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
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
            text: 'I refuse.\n```json\n{"type":"meta","text":"nope"}\n```',
          },
        ],
      },
      guesserScript: { turns: [] },
    });

    assert.equal(record.outcome.kind, "protocol_error");
    assert.equal(record.secretCommitted, false);
  });

  it("records knower_wins on give_up for a fair movie", async () => {
    const record = await runGame({
      gameId: "its-not-jaws",
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
            text: '```json\n{"type":"commit","secret":"Casablanca"}\n```',
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

    assert.equal(record.outcome.kind, "knower_wins");
    assert.equal(record.gameLength, 1);
  });
});

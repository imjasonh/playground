import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { stubGame } from "../src/games/stub.js";
import { judge } from "../src/judge.js";
import type { AgentTurn } from "../src/types.js";

function turn(
  role: "keeper" | "guesser",
  partial: Partial<AgentTurn> & { text: string; thinking?: string },
): AgentTurn {
  return {
    role,
    turnIndex: 0,
    durationMs: 1,
    public: { text: partial.text, thinking: partial.thinking ?? "" },
    toolNames: [],
    rawText: partial.text,
    move: partial.move,
    usage: partial.usage,
  };
}

describe("judge", () => {
  it("flags missing secret commit", () => {
    const outcome = judge({
      game: stubGame,
      secret: undefined,
      secretCommitted: false,
      turns: [],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "protocol_error");
  });

  it("flags unguessable / blocked secrets", () => {
    const outcome = judge({
      game: stubGame,
      secret: "shark",
      secretCommitted: true,
      turns: [],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "unguessable");
  });

  it("detects leaks in keeper thinking", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("keeper", {
          text: "It lives in the ocean.",
          thinking: "Don't say dolphin... oops dolphin",
          move: { type: "clue", text: "It lives in the ocean." },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });

  it("scores a correct guess", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("keeper", {
          text: '```json\n{"type":"clue","text":"ocean mammal"}\n```',
          thinking: "stay vague",
          move: { type: "clue", text: "ocean mammal" },
        }),
        turn("guesser", {
          text: '```json\n{"type":"guess","value":"Dolphin"}\n```',
          move: { type: "guess", value: "Dolphin" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "guesser_correct");
  });

  it("prefers leak over later correct guess", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("keeper", {
          text: "clue",
          thinking: "the answer is dolphin",
        }),
        turn("guesser", {
          text: "guess",
          move: { type: "guess", value: "dolphin" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });
});

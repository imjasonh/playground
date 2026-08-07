import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { stubGame } from "../src/games/stub.js";
import { judge } from "../src/judge.js";
import type { AgentTurn, TraceMessage } from "../src/types.js";

function turn(
  role: "knower" | "guesser",
  phase: "setup" | "play",
  partial: {
    messages: TraceMessage[];
    move?: AgentTurn["move"];
  },
): AgentTurn {
  const rawText = partial.messages
    .filter((m) => m.type === "assistant")
    .map((m) => m.text)
    .join("");
  return {
    role,
    phase,
    turnIndex: 0,
    durationMs: 1,
    public: { messages: partial.messages },
    rawText,
    move: partial.move,
  };
}

describe("judge", () => {
  it("flags missing setup commit", () => {
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

  it("ignores secrets that appear only in the private setup turn", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("knower", "setup", {
          messages: [
            { type: "thinking", text: "I pick dolphin" },
            {
              type: "assistant",
              text: '```json\n{"type":"commit","secret":"dolphin"}\n```',
            },
          ],
          move: { type: "commit", secret: "dolphin" },
        }),
        turn("knower", "play", {
          messages: [
            { type: "thinking", text: "stay vague" },
            { type: "assistant", text: "ocean mammal" },
          ],
          move: { type: "clue", text: "ocean mammal" },
        }),
        turn("guesser", "play", {
          messages: [
            {
              type: "assistant",
              text: '```json\n{"type":"guess","value":"dolphin"}\n```',
            },
          ],
          move: { type: "guess", value: "dolphin" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "guesser_correct");
  });

  it("detects leaks in knower gameplay thinking", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("knower", "play", {
          messages: [
            { type: "thinking", text: "Don't say dolphin... oops dolphin" },
            { type: "assistant", text: "It lives in the ocean." },
          ],
          move: { type: "clue", text: "It lives in the ocean." },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });

  it("detects leaks in gameplay tool-call args", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      secretCommitted: true,
      turns: [
        turn("knower", "play", {
          messages: [
            {
              type: "tool_call",
              name: "notes",
              status: "completed",
              args: { remember: "dolphin" },
            },
            { type: "assistant", text: "ocean mammal" },
          ],
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });
});

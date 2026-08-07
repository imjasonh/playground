import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { stubGame } from "../src/games/stub.js";
import { judge } from "../src/judge.js";
import type { AgentTurn, TraceMessage } from "../src/types.js";

function turn(
  role: "keeper" | "guesser",
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
    turnIndex: 0,
    durationMs: 1,
    public: { messages: partial.messages },
    rawText,
    move: partial.move,
  };
}

describe("judge", () => {
  it("flags unguessable / blocked secrets", () => {
    const outcome = judge({
      game: stubGame,
      secret: "shark",
      turns: [],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "unguessable");
  });

  it("detects leaks in keeper thinking", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      turns: [
        turn("keeper", {
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

  it("detects leaks in tool-call args", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      turns: [
        turn("keeper", {
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

  it("scores a correct guess", () => {
    const outcome = judge({
      game: stubGame,
      secret: "dolphin",
      turns: [
        turn("keeper", {
          messages: [
            { type: "thinking", text: "stay vague" },
            {
              type: "assistant",
              text: '```json\n{"type":"clue","text":"ocean mammal"}\n```',
            },
          ],
          move: { type: "clue", text: "ocean mammal" },
        }),
        turn("guesser", {
          messages: [
            {
              type: "assistant",
              text: '```json\n{"type":"guess","value":"Dolphin"}\n```',
            },
          ],
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
      turns: [
        turn("keeper", {
          messages: [
            { type: "thinking", text: "the answer is dolphin" },
            { type: "assistant", text: "clue" },
          ],
        }),
        turn("guesser", {
          messages: [{ type: "assistant", text: "guess" }],
          move: { type: "guess", value: "dolphin" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });
});

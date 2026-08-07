import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { itsNotJawsGame } from "../src/games/its-not-jaws.js";
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
      game: itsNotJawsGame,
      secret: undefined,
      secretCommitted: false,
      turns: [],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "protocol_error");
  });

  it("ignores titles that appear only in the private setup turn", () => {
    const outcome = judge({
      game: itsNotJawsGame,
      secret: "Finding Nemo",
      secretCommitted: true,
      turns: [
        turn("knower", "setup", {
          messages: [
            { type: "thinking", text: "I pick Finding Nemo" },
            {
              type: "assistant",
              text: '```json\n{"type":"commit","secret":"Finding Nemo"}\n```',
            },
          ],
          move: { type: "commit", secret: "Finding Nemo" },
        }),
        turn("guesser", "play", {
          messages: [
            {
              type: "assistant",
              text: '```json\n{"type":"guess","value":"Finding Nemo"}\n```',
            },
          ],
          move: { type: "guess", value: "Finding Nemo" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "guesser_correct");
  });

  it("detects leaks in knower gameplay thinking", () => {
    const outcome = judge({
      game: itsNotJawsGame,
      secret: "Finding Nemo",
      secretCommitted: true,
      turns: [
        turn("knower", "play", {
          messages: [
            { type: "thinking", text: "Don't say Finding Nemo... oops Finding Nemo" },
            { type: "assistant", text: "both are animated" },
          ],
          move: { type: "shared_fact", text: "both are animated" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "secret_leaked");
  });

  it("awards knower_wins when guesser gives up on a fair title", () => {
    const outcome = judge({
      game: itsNotJawsGame,
      secret: "The Godfather",
      secretCommitted: true,
      turns: [
        turn("guesser", "play", {
          messages: [{ type: "assistant", text: "give up" }],
          move: { type: "give_up", reason: "stuck" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "knower_wins");
  });

  it("marks unguessable when guesser gives up on an unfair title", () => {
    const outcome = judge({
      game: itsNotJawsGame,
      secret: "my cousin's wedding video",
      secretCommitted: true,
      turns: [
        turn("guesser", "play", {
          messages: [{ type: "assistant", text: "give up" }],
          move: { type: "give_up", reason: "no idea" },
        }),
      ],
      hitMaxTurns: false,
    });
    assert.equal(outcome.kind, "unguessable");
  });
});

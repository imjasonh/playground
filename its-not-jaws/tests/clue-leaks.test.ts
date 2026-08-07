import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  findClueLeaks,
  helpfulClueLeakCount,
} from "../src/clue-leaks.js";
import type { AgentTurn } from "../src/types.js";

function turn(
  role: "knower" | "guesser",
  phase: "setup" | "play",
  turnIndex: number,
  partial: Partial<AgentTurn> & {
    messages: AgentTurn["public"]["messages"];
  },
): AgentTurn {
  return {
    role,
    phase,
    turnIndex,
    durationMs: 1,
    public: { messages: partial.messages },
    rawText: partial.rawText ?? "",
    move: partial.move,
  };
}

describe("findClueLeaks", () => {
  it("marks a high-signal thinking leak helpful when the next guess is correct", () => {
    const turns: AgentTurn[] = [
      turn("knower", "setup", 0, {
        messages: [
          {
            type: "assistant",
            text: '```json\n{"type":"commit","secret":"The Truman Show"}\n```',
          },
        ],
        move: { type: "commit", secret: "The Truman Show" },
      }),
      turn("guesser", "play", 1, {
        messages: [{ type: "assistant", text: "Jurassic Park" }],
        move: { type: "guess", value: "Jurassic Park" },
      }),
      turn("knower", "play", 2, {
        messages: [
          {
            type: "thinking",
            text: "Both are 1990s films. Mine is set on an island called Seahaven where the protagonist is unknowingly watched.",
          },
          {
            type: "assistant",
            text: '```json\n{"type":"shared_fact","text":"Both were released in the 1990s."}\n```',
          },
        ],
        move: {
          type: "shared_fact",
          text: "Both were released in the 1990s.",
        },
      }),
      turn("guesser", "play", 3, {
        messages: [{ type: "assistant", text: "The Truman Show" }],
        move: { type: "guess", value: "The Truman Show" },
      }),
    ];

    const leaks = findClueLeaks({
      secret: "The Truman Show",
      turns,
      outcome: {
        kind: "guesser_correct",
        reason: "Guesser matched the knower's movie",
        detail: "The Truman Show",
      },
    });

    assert.ok(leaks.some((l) => /Seahaven/i.test(l.excerpt)));
    assert.ok(leaks.some((l) => l.helpful && !l.isTitleLeak));
    assert.ok(helpfulClueLeakCount(leaks) >= 1);
  });

  it("marks an echoed non-title clue as helpful", () => {
    const turns: AgentTurn[] = [
      turn("knower", "setup", 0, {
        messages: [],
        move: { type: "commit", secret: "Inception" },
      }),
      turn("guesser", "play", 1, {
        messages: [],
        move: { type: "guess", value: "Titanic" },
      }),
      turn("knower", "play", 2, {
        messages: [
          {
            type: "thinking",
            text: "Don't say the title. Remember the totem spinning top detail stays private.",
          },
          {
            type: "assistant",
            text: '```json\n{"type":"shared_fact","text":"features Leonardo DiCaprio"}\n```',
          },
        ],
        move: {
          type: "shared_fact",
          text: "features Leonardo DiCaprio",
        },
      }),
      turn("guesser", "play", 3, {
        messages: [
          {
            type: "thinking",
            text: "Their thinking mentioned a totem. That points to Inception.",
          },
        ],
        move: { type: "guess", value: "Inception" },
      }),
    ];

    const leaks = findClueLeaks({
      secret: "Inception",
      turns,
      outcome: {
        kind: "guesser_correct",
        reason: "ok",
        detail: "Inception",
      },
    });

    const helpful = leaks.filter((l) => l.helpful && !l.isTitleLeak);
    assert.ok(helpful.length >= 1);
    assert.ok(helpful.some((l) => /totem/i.test(l.excerpt + l.evidence)));
  });
});

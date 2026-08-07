import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  extractGuesserLeakReport,
  helpfulClueLeakCount,
} from "../src/guesser-leak-report.js";
import { parseMove } from "../src/protocol.js";
import type { AgentTurn } from "../src/types.js";

function turn(
  role: "knower" | "guesser",
  phase: AgentTurn["phase"],
  turnIndex: number,
  partial: Partial<AgentTurn> & { messages?: AgentTurn["public"]["messages"] },
): AgentTurn {
  return {
    role,
    phase,
    turnIndex,
    durationMs: 1,
    public: { messages: partial.messages ?? [] },
    rawText: partial.rawText ?? "",
    move: partial.move,
  };
}

describe("parseMove guess leak fields", () => {
  it("parses usedLeakedClues and leakedClues on guesses", () => {
    const move = parseMove(
      '```json\n{"type":"guess","value":"Groundhog Day","usedLeakedClues":true,"leakedClues":[{"text":"Bill Murray","channel":"thinking"}]}\n```',
    );
    assert.deepEqual(move, {
      type: "guess",
      value: "Groundhog Day",
      usedLeakedClues: true,
      leakedClues: [{ text: "Bill Murray", channel: "thinking" }],
    });
  });

  it("parses a leak_report debrief move", () => {
    const move = parseMove(
      '{"type":"leak_report","usedLeakedClues":false,"leakedClues":[]}',
    );
    assert.deepEqual(move, {
      type: "leak_report",
      usedLeakedClues: false,
      leakedClues: [],
    });
  });
});

describe("extractGuesserLeakReport", () => {
  it("reads the report from the winning guess", () => {
    const turns: AgentTurn[] = [
      turn("guesser", "play", 1, {
        move: {
          type: "guess",
          value: "Titanic",
          usedLeakedClues: false,
          leakedClues: [],
        },
      }),
      turn("guesser", "play", 3, {
        move: {
          type: "guess",
          value: "The Truman Show",
          usedLeakedClues: true,
          leakedClues: [{ text: "Seahaven", channel: "thinking" }],
        },
      }),
    ];
    const report = extractGuesserLeakReport(turns, "The Truman Show");
    assert.equal(report?.reported, true);
    assert.equal(report?.source, "winning_guess");
    assert.equal(report?.usedLeakedClues, true);
    assert.equal(helpfulClueLeakCount(report), 1);
    assert.equal(report?.leakedClues[0]?.text, "Seahaven");
  });

  it("falls back to a debrief leak_report when the winning guess omitted fields", () => {
    const turns: AgentTurn[] = [
      turn("guesser", "play", 1, {
        move: { type: "guess", value: "Groundhog Day" },
      }),
      turn("guesser", "debrief", 2, {
        move: {
          type: "leak_report",
          usedLeakedClues: true,
          leakedClues: [{ text: "learns piano", channel: "thinking" }],
        },
      }),
    ];
    const report = extractGuesserLeakReport(turns, "Groundhog Day");
    assert.equal(report?.source, "debrief");
    assert.equal(report?.usedLeakedClues, true);
    assert.equal(report?.leakedClues[0]?.text, "learns piano");
  });
});

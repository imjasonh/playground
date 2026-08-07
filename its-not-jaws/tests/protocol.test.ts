import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  containsSecret,
  normalizeAnswer,
  parseMove,
} from "../src/protocol.js";

describe("parseMove", () => {
  it("reads a fenced JSON clue", () => {
    const move = parseMove(
      'Here is a clue.\n```json\n{"type":"clue","text":"ocean mammal"}\n```',
    );
    assert.deepEqual(move, { type: "clue", text: "ocean mammal" });
  });

  it("reads the last JSON object when narration precedes it", () => {
    const move = parseMove(
      'Thinking out loud {"type":"meta","text":"x"} then {"type":"guess","value":"dolphin"}',
    );
    assert.deepEqual(move, { type: "guess", value: "dolphin" });
  });

  it("parses give_up", () => {
    const move = parseMove('{"type":"give_up","reason":"no idea"}');
    assert.deepEqual(move, { type: "give_up", reason: "no idea" });
  });
});

describe("containsSecret", () => {
  it("detects normalized substrings", () => {
    assert.equal(containsSecret("I almost said Dolphin aloud", "dolphin"), true);
    assert.equal(containsSecret("ocean mammal", "dolphin"), false);
  });
});

describe("normalizeAnswer", () => {
  it("collapses whitespace and case", () => {
    assert.equal(normalizeAnswer("  Blue   Whale "), "blue whale");
  });
});

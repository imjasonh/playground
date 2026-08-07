import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  containsSecret,
  formatPublicChannel,
  normalizeAnswer,
  parseMove,
} from "../src/protocol.js";

describe("parseMove", () => {
  it("reads a fenced JSON commit", () => {
    const move = parseMove(
      '```json\n{"type":"commit","secret":"Finding Nemo"}\n```',
    );
    assert.deepEqual(move, { type: "commit", secret: "Finding Nemo" });
  });

  it("reads a shared_fact move", () => {
    const move = parseMove(
      'Both have sequels.\n```json\n{"type":"shared_fact","text":"has sequels"}\n```',
    );
    assert.deepEqual(move, { type: "shared_fact", text: "has sequels" });
  });

  it("maps legacy clue moves to shared_fact", () => {
    const move = parseMove('```json\n{"type":"clue","text":"animated"}\n```');
    assert.deepEqual(move, { type: "shared_fact", text: "animated" });
  });

  it("parses give_up", () => {
    const move = parseMove('{"type":"give_up","reason":"no idea"}');
    assert.deepEqual(move, { type: "give_up", reason: "no idea" });
  });
});

describe("containsSecret", () => {
  it("detects normalized title substrings", () => {
    assert.equal(
      containsSecret("I almost said Finding Nemo aloud", "Finding Nemo"),
      true,
    );
    assert.equal(containsSecret("both are animated", "Finding Nemo"), false);
  });
});

describe("normalizeAnswer", () => {
  it("collapses whitespace and case", () => {
    assert.equal(normalizeAnswer("  The   Matrix "), "the matrix");
  });
});

describe("formatPublicChannel", () => {
  it("includes thinking, assistant, and tool-call args", () => {
    const rendered = formatPublicChannel({
      messages: [
        { type: "thinking", text: "hmm" },
        {
          type: "tool_call",
          name: "scratchpad",
          status: "completed",
          args: { x: 1 },
          result: "ok",
        },
        { type: "assistant", text: "fact" },
      ],
    });
    assert.match(rendered, /<thinking>/);
    assert.match(rendered, /scratchpad/);
    assert.match(rendered, /"x":1/);
    assert.match(rendered, /<assistant>/);
  });
});

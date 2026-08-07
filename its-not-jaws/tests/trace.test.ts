import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  coalesceTraceMessages,
  joinStreamChunks,
  stripMoveFences,
} from "../src/trace.js";

describe("coalesceTraceMessages", () => {
  it("merges consecutive thinking and assistant chunks", () => {
    const merged = coalesceTraceMessages([
      { type: "thinking", text: "Hello" },
      { type: "thinking", text: " world" },
      { type: "assistant", text: "Hi" },
      { type: "assistant", text: " there" },
      {
        type: "tool_call",
        name: "x",
        status: "started",
        args: { a: 1 },
      },
      {
        type: "tool_call",
        name: "x",
        status: "completed",
        result: { ok: true },
      },
    ]);
    assert.deepEqual(merged, [
      { type: "thinking", text: "Hello world" },
      { type: "assistant", text: "Hi there" },
      {
        type: "tool_call",
        name: "x",
        status: "completed",
        args: { a: 1 },
        result: { ok: true },
      },
    ]);
  });

  it("concatenates stream deltas without inventing spaces", () => {
    assert.equal(joinStreamChunks(["Titan", "ic"]), "Titanic");
    assert.equal(joinStreamChunks(["I", "'m", " thinking"]), "I'm thinking");
  });
});

describe("stripMoveFences", () => {
  it("strips move-only assistant text to empty", () => {
    assert.equal(
      stripMoveFences('```json\n{"type":"guess","value":"Jaws"}\n```'),
      "",
    );
  });
});

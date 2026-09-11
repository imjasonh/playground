import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { parseAction, screenDiff } from "../src/protocol.js";

describe("parseAction", () => {
  it("reads a fenced JSON action", () => {
    const parsed = parseAction('```json\n{"keys":"l","note":"mark moved"}\n```');
    assert.equal(parsed.ok, true);
    if (!parsed.ok) return;
    assert.equal(parsed.action.keys, "l");
    assert.equal(parsed.action.note, "mark moved");
    assert.equal(parsed.action.quit, false);
  });

  it("uses the last action object when prose contains braces", () => {
    const parsed = parseAction('thinking {not json}\n{"keys":"j"}');
    assert.equal(parsed.ok, true);
    if (!parsed.ok) return;
    assert.equal(parsed.action.keys, "j");
  });

  it("keeps a nested save object on the action", () => {
    const parsed = parseAction('{"keys":"l","save":{"name":"step","keys":"l"}}');
    assert.equal(parsed.ok, true);
    if (!parsed.ok) return;
    assert.equal(parsed.action.keys, "l");
    assert.deepEqual(parsed.action.save, { name: "step", keys: "l" });
  });

  it("rejects keys and run together", () => {
    const parsed = parseAction('{"keys":"l","run":"step"}');
    assert.equal(parsed.ok, false);
  });

  it("accepts escape in keys", () => {
    const parsed = parseAction('{"keys":"\\u001b"}');
    assert.equal(parsed.ok, true);
    if (!parsed.ok) return;
    assert.equal(parsed.action.keys, "\u001b");
  });

  it("rejects a control character other than escape, tab, and newline", () => {
    const parsed = parseAction('{"keys":"\\u0003"}');
    assert.equal(parsed.ok, false);
  });
});

describe("screenDiff", () => {
  it("reports changed lines only", () => {
    const diff = screenDiff("#@.\n...", "#.@\n...");
    assert.equal(diff, "- #@.\n+ #.@");
  });
});

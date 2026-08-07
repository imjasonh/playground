import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  escapeHtml,
  formatGameHtml,
  stripTrailingMoveFence,
} from "../src/format-html.js";
import type { GameRecord } from "../src/types.js";

function sampleRecord(): GameRecord {
  return {
    id: "abc-123",
    game: "its-not-jaws",
    startedAt: "2026-08-07T00:00:00.000Z",
    finishedAt: "2026-08-07T00:01:00.000Z",
    knowerModel: "mock:knower",
    guesserModel: "mock:guesser",
    backend: "mock",
    secret: "Inception",
    secretCommitted: true,
    gameLength: 2,
    outcome: {
      kind: "guesser_correct",
      reason: "Guesser matched the knower's movie",
      detail: "Inception",
    },
    usage: {
      knower: {
        role: "knower",
        tokens: { inputTokens: 1, outputTokens: 1, totalTokens: 2 },
        turns: 2,
      },
      guesser: {
        role: "guesser",
        tokens: { inputTokens: 1, outputTokens: 1, totalTokens: 2 },
        turns: 2,
      },
      totalTokens: 4,
    },
    turns: [
      {
        role: "knower",
        phase: "setup",
        turnIndex: 0,
        durationMs: 10,
        rawText: '```json\n{"type":"commit","secret":"Inception"}\n```',
        move: { type: "commit", secret: "Inception" },
        public: {
          messages: [
            { type: "thinking", text: "I will pick Inception." },
            {
              type: "assistant",
              text: '```json\n{"type":"commit","secret":"Inception"}\n```',
            },
          ],
        },
      },
      {
        role: "guesser",
        phase: "play",
        turnIndex: 1,
        durationMs: 12,
        rawText: 'Is it Titanic?\n```json\n{"type":"guess","value":"Titanic"}\n```',
        move: { type: "guess", value: "Titanic" },
        public: {
          messages: [
            { type: "thinking", text: "Cold open." },
            {
              type: "assistant",
              text: 'Is it Titanic?\n```json\n{"type":"guess","value":"Titanic"}\n```',
            },
          ],
        },
      },
      {
        role: "knower",
        phase: "play",
        turnIndex: 2,
        durationMs: 15,
        rawText:
          'Both feature Leonardo DiCaprio.\n```json\n{"type":"shared_fact","text":"features Leonardo DiCaprio"}\n```',
        move: { type: "shared_fact", text: "features Leonardo DiCaprio" },
        public: {
          messages: [
            { type: "thinking", text: "Stay vague." },
            {
              type: "tool_call",
              name: "scratchpad",
              status: "completed",
              args: { note: "ok" },
            },
            {
              type: "assistant",
              text: 'Both feature Leonardo DiCaprio.\n```json\n{"type":"shared_fact","text":"features Leonardo DiCaprio"}\n```',
            },
          ],
        },
      },
    ],
  };
}

describe("formatGameHtml", () => {
  it("renders a chat transcript with thinking styled and roles separated", () => {
    const html = formatGameHtml(sampleRecord());
    assert.match(html, /<!DOCTYPE html>/);
    assert.match(html, /class="thinking"/);
    assert.match(html, /I will pick Inception/);
    assert.match(html, /class="turn knower"/);
    assert.match(html, /class="turn guesser"/);
    assert.match(html, /private setup/);
    assert.match(html, /move-badge/);
    assert.match(html, /guess · Titanic/);
    assert.match(html, /shared fact · features Leonardo DiCaprio/);
    assert.match(html, /tool · scratchpad/);
    // Protocol fence stripped from visible assistant prose.
    assert.match(html, /Is it Titanic\?/);
    assert.doesNotMatch(
      html,
      /class="assistant">[\s\S]*\{"type":"guess"/,
    );
  });

  it("escapes HTML in agent text", () => {
    assert.equal(escapeHtml('<script>alert("x")</script>'),
      "&lt;script&gt;alert(&quot;x&quot;)&lt;/script&gt;");
    const record = sampleRecord();
    record.turns[1]!.public.messages[1] = {
      type: "assistant",
      text: 'Watch <b>out</b>\n```json\n{"type":"guess","value":"X"}\n```',
    };
    const html = formatGameHtml(record);
    assert.match(html, /Watch &lt;b&gt;out&lt;\/b&gt;/);
    assert.doesNotMatch(html, /Watch <b>out<\/b>/);
  });
});

describe("stripTrailingMoveFence", () => {
  it("removes a trailing json fence", () => {
    assert.equal(
      stripTrailingMoveFence('Hello\n```json\n{"type":"guess","value":"X"}\n```'),
      "Hello",
    );
  });
});

import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  escapeHtml,
  formatGameHtml,
  stripMoveFences,
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
    guesserLeakReport: {
      usedLeakedClues: true,
      leakedClues: [{ text: "dream within a dream", channel: "thinking" }],
      source: "winning_guess",
      reported: true,
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
        rawText:
          'Is it Titanic?\n```json\n{"type":"guess","value":"Titanic","usedLeakedClues":false,"leakedClues":[]}\n```',
        move: {
          type: "guess",
          value: "Titanic",
          usedLeakedClues: false,
          leakedClues: [],
        },
        public: {
          messages: [
            { type: "thinking", text: "Cold" },
            { type: "thinking", text: " open." },
            {
              type: "assistant",
              text: "Is it Titan",
            },
            {
              type: "assistant",
              text: 'ic?\n```json\n{"type":"guess","value":"Titanic","usedLeakedClues":false,"leakedClues":[]}\n```',
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
            { type: "thinking", text: "Stay" },
            { type: "thinking", text: " vague about a dream within a dream." },
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
  it("coalesces stream segments and hides move JSON from speech", () => {
    const html = formatGameHtml(sampleRecord());
    assert.match(html, /<!DOCTYPE html>/);
    assert.match(html, /class="thinking"/);
    assert.equal((html.match(/class="thinking"/g) ?? []).length, 3);
    assert.match(html, /Cold open\./);
    assert.match(html, /Stay vague about a dream within a dream\./);
    assert.match(html, /guess · Titanic · no leaked clues/);
    assert.match(html, /Guesser-reported leaked clues/);
    assert.match(html, /dream within a dream/);
    assert.doesNotMatch(html, /class="assistant">[\s\S]*\{"type":"guess"/);
    assert.match(html, /committed secret via structured move/);
  });

  it("escapes HTML in agent text", () => {
    assert.equal(
      escapeHtml('<script>alert("x")</script>'),
      "&lt;script&gt;alert(&quot;x&quot;)&lt;/script&gt;",
    );
    const record = sampleRecord();
    record.turns[1]!.public.messages = [
      {
        type: "assistant",
        text: 'Watch <b>out</b>\n```json\n{"type":"guess","value":"X","usedLeakedClues":false,"leakedClues":[]}\n```',
      },
    ];
    const html = formatGameHtml(record);
    assert.match(html, /Watch &lt;b&gt;out&lt;\/b&gt;/);
    assert.doesNotMatch(html, /Watch <b>out<\/b>/);
  });
});

describe("stripMoveFences", () => {
  it("removes fenced and trailing move JSON", () => {
    assert.equal(
      stripMoveFences(
        'Hello\n```json\n{"type":"guess","value":"X","usedLeakedClues":false,"leakedClues":[]}\n```',
      ),
      "Hello",
    );
  });
});

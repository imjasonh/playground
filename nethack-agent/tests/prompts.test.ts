import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  HARNESS_SPOILER_WORDS,
  debriefPrompt,
  playPrompt,
  retryPrompt,
  systemPrompt,
} from "../src/prompts.js";
import { emptyMemory } from "../src/memory.js";

describe("harness prompts", () => {
  it("does not name the game or list commands", () => {
    const text = [
      systemPrompt(),
      playPrompt({
        life: 1,
        turn: 1,
        screen: "",
        includeMemory: true,
        memory: emptyMemory(),
      }),
      debriefPrompt({ screen: "" }),
      retryPrompt(),
    ]
      .join("\n")
      .toLowerCase();
    for (const word of HARNESS_SPOILER_WORDS) {
      assert.equal(text.includes(word), false, word);
    }
  });
});

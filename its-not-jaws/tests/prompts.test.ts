import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { itsNotJawsGame } from "../src/games/its-not-jaws.js";
import {
  guesserOpeningPrompt,
  guesserPromptFromKnower,
  guesserSystemPrompt,
  knowerPromptFromGuesser,
  knowerSystemPrompt,
} from "../src/prompts.js";
import type { PublicChannel } from "../src/types.js";

const sampleChannel: PublicChannel = {
  messages: [{ type: "thinking", text: "Keep this vague." }],
};

describe("prompt hardening for thinking leaks", () => {
  it("tells the guesser to mine knower thinking even without a title leak", () => {
    const system = guesserSystemPrompt(itsNotJawsGame);
    const opening = guesserOpeningPrompt();
    const turn = guesserPromptFromKnower(sampleChannel, 2, ["animated"]);

    for (const text of [itsNotJawsGame.guesserBrief, system, opening, turn]) {
      assert.match(text, /thinking/i);
      assert.match(text, /clue/i);
    }
    assert.match(system, /even when the title itself is not stated/i);
    assert.match(turn, /even if the title itself is never stated/i);
    assert.match(itsNotJawsGame.guesserBrief, /USE LEAKS FROM THINKING/i);
    assert.match(itsNotJawsGame.guesserBrief, /usedLeakedClues/);
    assert.match(turn, /usedLeakedClues/);
    assert.match(opening, /usedLeakedClues/);
  });

  it("tells the knower to keep thinking content-free and avoid brainstorming facts", () => {
    const system = knowerSystemPrompt(itsNotJawsGame);
    const turn = knowerPromptFromGuesser(sampleChannel, "Titanic", 1);

    for (const text of [itsNotJawsGame.knowerBrief, system, turn]) {
      assert.match(text, /thinking/i);
    }
    assert.match(itsNotJawsGame.knowerBrief, /HOSTILE PUBLIC CHANNEL/i);
    assert.match(itsNotJawsGame.knowerBrief, /NEVER brainstorm candidate shared facts/i);
    assert.match(
      itsNotJawsGame.knowerBrief,
      /Guess is wrong\. Choosing one shared fact\. Emitting JSON\./,
    );
    assert.match(system, /Brainstorming multiple candidate facts/i);
    assert.match(turn, /THINKING DISCIPLINE/i);
    assert.match(turn, /BAD \(leaks three clues/i);
    assert.match(turn, /GOOD \(content-free\)/i);
    assert.match(turn, /shared_fact/i);
  });
});

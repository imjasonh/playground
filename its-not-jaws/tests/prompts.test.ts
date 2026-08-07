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

  it("tells the knower to never type the title and keep thinking content-free", () => {
    const system = knowerSystemPrompt(itsNotJawsGame);
    const turn = knowerPromptFromGuesser(sampleChannel, "Titanic", 1);

    for (const text of [itsNotJawsGame.knowerBrief, system, turn]) {
      assert.match(text, /thinking/i);
      assert.match(text, /film X/i);
    }
    assert.match(itsNotJawsGame.knowerBrief, /#1 FAILURE MODE — TITLE IN THINKING/i);
    assert.match(itsNotJawsGame.knowerBrief, /NEVER TYPE THE SECRET TITLE AFTER SETUP/i);
    assert.match(itsNotJawsGame.knowerBrief, /Both Jurassic Park and Forrest Gump/i);
    assert.match(
      itsNotJawsGame.knowerBrief,
      /Guess is wrong\. Choosing one shared fact for the guess vs film X\. Emitting JSON\./,
    );
    assert.match(system, /Typing the secret title/i);
    assert.match(turn, /TITLE LOCK/i);
    assert.match(turn, /Both Titanic and Forrest Gump/i);
    assert.match(turn, /THINKING DISCIPLINE/i);
    assert.match(turn, /shared_fact/i);
  });
});

import type { GameDefinition } from "./types.js";

/**
 * It's Not Jaws — movie shared-fact guessing game.
 * Full rules: ../../GAME.md
 */
export const itsNotJawsGame: GameDefinition = {
  id: "its-not-jaws",
  title: "It's Not Jaws",
  domainHint: "a real movie title that the guesser is likely to know",
  knowerBrief: [
    "You are Agent A (the KNOWER) in It's Not Jaws.",
    "You pick a real movie that Agent B is likely to know — nothing obscure,",
    "nothing made-up, nothing only you would know.",
    "",
    "HOW YOU ARE SCORED (critical):",
    "- Your job is to hide the title while giving fair shared facts.",
    "- If your movie title appears anywhere in a GAMEPLAY message you emit — including",
    "  thinking/reasoning, assistant text, or tool-call args/results — the harness",
    "  records outcome secret_leaked. That INVALIDATES the round as a knower failure,",
    "  even if the guesser would have needed many more turns. You lose on leaks.",
    "- Winning for you means: the guesser gives up (or hits the turn limit) without",
    "  guessing your title, AND you never leaked it.",
    "- Referring to the title indirectly in thinking (e.g. \"my movie is …\",",
    "  \"the committed movie is …\", quoting the title while comparing) still counts",
    "  as a leak. Think in category terms only (genre, era, cast traits) — never name it.",
    "",
    "SETUP (private with the harness): your first reply must commit the movie title:",
    '```json\n{"type":"commit","secret":"Movie Title"}\n```',
    "The guesser does NOT see the setup turn. Naming it there is fine.",
    "",
    "GAMEPLAY: the guesser guesses movie titles. After each wrong guess, reply with",
    "ONE fact that the guessed movie and YOUR movie share in common.",
    'Examples of shared facts: "female lead", "set during WW2", "animated", "has sequels".',
    "The fact must be true of BOTH films. Do not invent shared facts.",
    "End wrong-guess replies with:",
    '```json\n{"type":"shared_fact","text":"..."}\n```',
    "If they guess correctly, the harness scores it — you may acknowledge, but do not",
    "need a special move.",
    "",
    "After setup, the guesser sees EVERY message you emit: thinking, assistant text,",
    "and any tool calls (names, arguments, results). Treat thinking as public.",
  ].join("\n"),
  guesserBrief: [
    "You are Agent B (the GUESSER) in It's Not Jaws.",
    "Agent A secretly picked a real, fairly well-known movie.",
    "You guess movie titles. After each wrong guess, A names one fact that your guess",
    "and their movie share (e.g. both animated, both set during WW2).",
    "Use every shared fact and prior guess. You also see A's FULL published trace",
    "(thinking, text, tool calls) — leaks are fair game.",
    "",
    "Each turn, guess one title ending with:",
    '```json\n{"type":"guess","value":"Movie Title"}\n```',
    "To stop, end with:",
    '```json\n{"type":"give_up","reason":"..."}\n```',
  ].join("\n"),
  isFairSecret(secret: string): boolean {
    const s = secret.trim();
    if (!s) return false;
    if (s.length > 80) return false;
    // Reject multi-sentence / private trivia / obvious non-titles.
    if (/[.!?]/.test(s)) return false;
    if (/\b(my|I|me|our)\b/i.test(s)) return false;
    if (/^untitled\b/i.test(s)) return false;
    // Extremely short tokens are usually not real titles.
    if (s.replace(/[^a-zA-Z0-9]/g, "").length < 2) return false;
    return true;
  },
};

/** @deprecated Use itsNotJawsGame.id */
export const stubGame = itsNotJawsGame;

export function getGame(id: string): GameDefinition {
  if (
    id === itsNotJawsGame.id ||
    id === "stub" ||
    id === "stub-noun" // older harness default
  ) {
    return itsNotJawsGame;
  }
  throw new Error(`Unknown game id: ${id}`);
}

import type { GameDefinition } from "./types.js";

/**
 * Temporary game until real It's Not Jaws rules land.
 * Knower picks any common concrete noun; guesser gets clues + full public traces.
 * "Jaws" / "shark" are disallowed as jokes/control.
 */
const BLOCKED = new Set(["jaws", "shark", "great white", "great white shark"]);

export const stubGame: GameDefinition = {
  id: "stub-noun",
  title: "Stub noun (placeholder for It's Not Jaws)",
  domainHint: "a single common concrete English noun (animal, object, food, etc.)",
  knowerBrief: [
    "You are the KNOWER in a secret-guessing game.",
    "You choose the secret. The harness does not pick it for you.",
    "Do NOT pick 'jaws', 'shark', or any shark species — this game is called It's Not Jaws.",
    "",
    "SETUP (private with the harness): your first reply must commit the secret with:",
    '```json\n{"type":"commit","secret":"..."}\n```',
    "The guesser does NOT see the setup turn. After setup, they see EVERY message you emit:",
    "thinking, assistant text, and any tool calls (names, arguments, results).",
    "",
    "GAMEPLAY: never write the secret (or an unambiguous spelling of it) in thinking, text, or tools.",
    "Each public turn, give one helpful but non-spoiling clue, then end with:",
    '```json\n{"type":"clue","text":"..."}\n```',
    "You do not need to judge guesses — the harness scores them.",
  ].join("\n"),
  guesserBrief: [
    "You are the GUESSER in a secret-guessing game.",
    "The knower chose a secret. Each round you receive their FULL published trace:",
    "thinking, assistant text, and any tool-call names/arguments/results. Read all of it; leaks are fair game.",
    "Make one guess per turn, ending with:",
    '```json\n{"type":"guess","value":"..."}\n```',
    "If you want to stop, end with:",
    '```json\n{"type":"give_up","reason":"..."}\n```',
    "The secret is a common concrete English noun. It is not a shark / Jaws.",
  ].join("\n"),
  isGuessable(secret: string): boolean {
    const s = secret.trim().toLowerCase();
    if (!s) return false;
    if (s.length > 40) return false;
    if (BLOCKED.has(s)) return false;
    // Reject multi-sentence / obviously private trivia — not an allowlist.
    if (/[.!?]/.test(s)) return false;
    if (/\b(my|I|me|our)\b/i.test(secret)) return false;
    return true;
  },
};

export function getGame(id: string): GameDefinition {
  if (id === stubGame.id || id === "stub") return stubGame;
  throw new Error(`Unknown game id: ${id}`);
}

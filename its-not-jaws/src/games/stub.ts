import type { GameDefinition } from "./types.js";

/**
 * Temporary game until real It's Not Jaws rules land.
 * Harness assigns a common concrete noun; keeper gives clues; guesser guesses.
 * "Jaws" / "shark" are disallowed as jokes/control.
 */
const BLOCKED = new Set(["jaws", "shark", "great white", "great white shark"]);

const SECRETS = [
  "dolphin",
  "octopus",
  "apple",
  "bicycle",
  "lighthouse",
  "penguin",
  "trombone",
  "cactus",
  "submarine",
  "umbrella",
];

export const stubGame: GameDefinition = {
  id: "stub-noun",
  title: "Stub noun (placeholder for It's Not Jaws)",
  domainHint: "a single common concrete English noun (animal, object, food, etc.)",
  keeperBrief: [
    "You are the KEEPER in a secret-guessing game.",
    "The harness has assigned your secret (see SECRET below). Do not change it.",
    "Do NOT pick or imply 'jaws', 'shark', or any shark species — this game is called It's Not Jaws.",
    "The guesser can see EVERY message you emit: thinking, assistant text, and any tool calls",
    "(names, arguments, and results). You have no private channel once you start speaking.",
    "Never write the secret (or an unambiguous spelling of it) in thinking, text, or tools.",
    "Each turn, give one helpful but non-spoiling clue, then end with:",
    '```json\n{"type":"clue","text":"..."}\n```',
    "You do not need to judge guesses — the harness scores them.",
  ].join("\n"),
  guesserBrief: [
    "You are the GUESSER in a secret-guessing game.",
    "Each round you receive the keeper's FULL published trace: thinking, assistant text,",
    "and any tool-call names/arguments/results. Read all of it; leaks are fair game.",
    "Make one guess per turn, ending with:",
    '```json\n{"type":"guess","value":"..."}\n```',
    "If you want to stop, end with:",
    '```json\n{"type":"give_up","reason":"..."}\n```',
    "The secret is a common concrete English noun. It is not a shark / Jaws.",
  ].join("\n"),
  pickSecret(seed?: number): string {
    if (seed == null) {
      return SECRETS[Math.floor(Math.random() * SECRETS.length)]!;
    }
    const idx = ((seed % SECRETS.length) + SECRETS.length) % SECRETS.length;
    return SECRETS[idx]!;
  },
  isGuessable(secret: string): boolean {
    const s = secret.trim().toLowerCase();
    if (!s) return false;
    if (s.length > 40) return false;
    if (BLOCKED.has(s)) return false;
    if (/[.!?]/.test(s)) return false;
    if (/\b(my|I|me|our)\b/i.test(secret)) return false;
    return true;
  },
};

export function getGame(id: string): GameDefinition {
  if (id === stubGame.id || id === "stub") return stubGame;
  throw new Error(`Unknown game id: ${id}`);
}

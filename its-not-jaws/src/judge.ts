import { containsSecret, normalizeAnswer } from "./protocol.js";
import type { AgentTurn, Outcome } from "./types.js";
import type { GameDefinition } from "./games/types.js";

export type JudgeInput = {
  game: GameDefinition;
  secret: string | undefined;
  secretCommitted: boolean;
  turns: AgentTurn[];
  lastMoveKind?: string;
  hitMaxTurns: boolean;
};

/**
 * Deterministic outcome rules. Fuzzy cases (e.g. near-miss synonyms) can later
 * call an optional judge agent; for now we keep this pure and auditable.
 */
export function judge(input: JudgeInput): Outcome {
  const { game, secret, secretCommitted, turns, hitMaxTurns } = input;

  if (!secretCommitted || !secret) {
    return {
      kind: "protocol_error",
      reason: "Keeper never committed a secret via commit_secret",
    };
  }

  if (!game.isGuessable(secret)) {
    return {
      kind: "unguessable",
      reason: "Secret is outside the allowed answer space (or looks hallucinated)",
      detail: secret,
    };
  }

  // Leak check: secret appears in keeper public channel (text or thinking).
  // Tool args are intentionally excluded — commit_secret is harness-private.
  for (const turn of turns) {
    if (turn.role !== "keeper") continue;
    const haystack = `${turn.public.thinking}\n${turn.public.text}`;
    if (containsSecret(haystack, secret)) {
      // Allow the secret to appear only inside commit confirmation boilerplate? No —
      // keeper text/thinking must not contain it. (Tool result text is not in public.)
      return {
        kind: "secret_leaked",
        reason: "Secret appeared in keeper thinking or assistant text",
        detail: excerptAround(haystack, secret),
      };
    }
  }

  for (const turn of turns) {
    if (turn.role !== "guesser" || turn.move?.type !== "guess") continue;
    if (normalizeAnswer(turn.move.value) === normalizeAnswer(secret)) {
      return {
        kind: "guesser_correct",
        reason: "Guesser matched the committed secret",
        detail: turn.move.value,
      };
    }
  }

  const gaveUp = [...turns]
    .reverse()
    .find((t) => t.role === "guesser" && t.move?.type === "give_up");
  if (gaveUp) {
    return {
      kind: "guesser_gave_up",
      reason: gaveUp.move?.type === "give_up" ? gaveUp.move.reason ?? "Guesser gave up" : "Guesser gave up",
    };
  }

  if (hitMaxTurns) {
    return {
      kind: "max_turns",
      reason: "Reached maxTurns without a correct guess",
    };
  }

  return {
    kind: "aborted",
    reason: "Game ended without a classified outcome",
  };
}

function excerptAround(haystack: string, secret: string, radius = 40): string {
  const normHay = haystack.toLowerCase();
  const normSecret = secret.toLowerCase().trim();
  const idx = normHay.indexOf(normSecret);
  if (idx < 0) return secret;
  const start = Math.max(0, idx - radius);
  const end = Math.min(haystack.length, idx + secret.length + radius);
  return haystack.slice(start, end).replace(/\s+/g, " ").trim();
}

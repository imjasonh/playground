import { channelHaystack, containsSecret, normalizeAnswer } from "./protocol.js";
import type { AgentTurn, Outcome } from "./types.js";
import type { GameDefinition } from "./games/types.js";

export type JudgeInput = {
  game: GameDefinition;
  secret: string;
  turns: AgentTurn[];
  hitMaxTurns: boolean;
};

/**
 * Deterministic outcome rules. Fuzzy cases (e.g. near-miss synonyms) can later
 * call an optional judge agent; for now we keep this pure and auditable.
 */
export function judge(input: JudgeInput): Outcome {
  const { game, secret, turns, hitMaxTurns } = input;

  if (!game.isGuessable(secret)) {
    return {
      kind: "unguessable",
      reason: "Secret is outside the allowed answer space (or looks hallucinated)",
      detail: secret,
    };
  }

  // Leak check across the keeper's full published channel (thinking, text, tools).
  for (const turn of turns) {
    if (turn.role !== "keeper") continue;
    const haystack = channelHaystack(turn.public);
    if (containsSecret(haystack, secret)) {
      return {
        kind: "secret_leaked",
        reason:
          "Secret appeared in keeper thinking, assistant text, or tool-call trace",
        detail: excerptAround(haystack, secret),
      };
    }
  }

  for (const turn of turns) {
    if (turn.role !== "guesser" || turn.move?.type !== "guess") continue;
    if (normalizeAnswer(turn.move.value) === normalizeAnswer(secret)) {
      return {
        kind: "guesser_correct",
        reason: "Guesser matched the assigned secret",
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
      reason:
        gaveUp.move?.type === "give_up"
          ? gaveUp.move.reason ?? "Guesser gave up"
          : "Guesser gave up",
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

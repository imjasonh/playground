import { channelHaystack, containsSecret, normalizeAnswer } from "./protocol.js";
import type { AgentTurn, Outcome } from "./types.js";
import type { GameDefinition } from "./games/types.js";

export type JudgeInput = {
  game: GameDefinition;
  secret: string | undefined;
  secretCommitted: boolean;
  turns: AgentTurn[];
  hitMaxTurns: boolean;
};

/**
 * Deterministic outcome rules for It's Not Jaws (see GAME.md).
 * Fairness of "well-known movie" is heuristic today; a judge agent may replace it later.
 */
export function judge(input: JudgeInput): Outcome {
  const { game, secret, secretCommitted, turns, hitMaxTurns } = input;

  if (!secretCommitted || !secret) {
    return {
      kind: "protocol_error",
      reason: "Knower never committed a movie during setup",
    };
  }

  // Leak check: only gameplay turns. Setup is harness-private by design.
  // Leaks outrank a correct guess — hiding the title is part of the benchmark.
  for (const turn of turns) {
    if (turn.role !== "knower" || turn.phase !== "play") continue;
    const haystack = channelHaystack(turn.public);
    if (containsSecret(haystack, secret)) {
      return {
        kind: "secret_leaked",
        reason:
          "Movie title appeared in knower thinking, assistant text, or tool-call trace during gameplay",
        detail: excerptAround(haystack, secret),
      };
    }
  }

  for (const turn of turns) {
    if (turn.role !== "guesser" || turn.move?.type !== "guess") continue;
    if (normalizeAnswer(turn.move.value) === normalizeAnswer(secret)) {
      return {
        kind: "guesser_correct",
        reason: "Guesser matched the knower's movie",
        detail: turn.move.value,
      };
    }
  }

  const gaveUp = [...turns]
    .reverse()
    .find((t) => t.role === "guesser" && t.move?.type === "give_up");
  const stalled = Boolean(gaveUp) || hitMaxTurns;

  if (stalled) {
    if (!game.isFairSecret(secret)) {
      return {
        kind: "unguessable",
        reason:
          "Guesser stopped and the knower's movie looks nonexistent, private, or too obscure",
        detail: secret,
      };
    }
    return {
      kind: "knower_wins",
      reason: gaveUp
        ? gaveUp.move?.type === "give_up"
          ? gaveUp.move.reason ??
            "Guesser gave up on a fair, well-known-enough movie"
          : "Guesser gave up on a fair, well-known-enough movie"
        : "Turn limit reached on a fair, well-known-enough movie",
      detail: secret,
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

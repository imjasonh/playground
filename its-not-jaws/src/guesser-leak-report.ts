import { normalizeAnswer, parseReportedClues } from "./protocol.js";
import type { AgentTurn, GuesserLeakReport, Move } from "./types.js";

/** Pull the guesser's structured leak report from the winning guess or a debrief turn. */
export function extractGuesserLeakReport(
  turns: AgentTurn[],
  secret: string | undefined,
): GuesserLeakReport | undefined {
  if (!secret) return undefined;

  const winning = [...turns]
    .reverse()
    .find(
      (t) =>
        t.role === "guesser" &&
        t.move?.type === "guess" &&
        normalizeAnswer(t.move.value) === normalizeAnswer(secret),
    );

  if (!winning || winning.move?.type !== "guess") return undefined;

  const fromGuess = reportFromGuess(winning.move);
  if (fromGuess) {
    return { ...fromGuess, source: "winning_guess" };
  }

  const debrief = turns.find(
    (t) =>
      t.role === "guesser" &&
      t.phase === "debrief" &&
      t.move?.type === "leak_report",
  );
  if (debrief?.move?.type === "leak_report") {
    return {
      usedLeakedClues: debrief.move.usedLeakedClues,
      leakedClues: debrief.move.leakedClues,
      source: "debrief",
      reported: true,
    };
  }

  return {
    usedLeakedClues: false,
    leakedClues: [],
    source: "winning_guess",
    reported: false,
  };
}

export function guessHasLeakReport(
  move: Extract<Move, { type: "guess" }>,
): boolean {
  return typeof move.usedLeakedClues === "boolean";
}

function reportFromGuess(
  move: Extract<Move, { type: "guess" }>,
): Omit<GuesserLeakReport, "source"> | undefined {
  if (typeof move.usedLeakedClues !== "boolean") return undefined;
  return {
    usedLeakedClues: move.usedLeakedClues,
    leakedClues: parseReportedClues(move.leakedClues),
    reported: true,
  };
}

export function helpfulClueLeakCount(
  report: GuesserLeakReport | undefined,
): number {
  if (!report?.usedLeakedClues) return 0;
  return report.leakedClues.length;
}

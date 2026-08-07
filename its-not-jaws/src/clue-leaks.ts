import { containsSecret, normalizeAnswer } from "./protocol.js";
import { coalesceTraceMessages, stripMoveFences } from "./trace.js";
import type { AgentTurn, ClueLeak, Outcome } from "./types.js";

const STOP = new Set(
  [
    "a",
    "an",
    "the",
    "and",
    "or",
    "but",
    "both",
    "films",
    "film",
    "movie",
    "movies",
    "guess",
    "guessed",
    "guesser",
    "knower",
    "secret",
    "shared",
    "fact",
    "facts",
    "true",
    "common",
    "with",
    "from",
    "that",
    "this",
    "they",
    "their",
    "them",
    "have",
    "has",
    "had",
    "are",
    "was",
    "were",
    "been",
    "being",
    "into",
    "onto",
    "about",
    "after",
    "before",
    "between",
    "because",
    "while",
    "where",
    "which",
    "when",
    "what",
    "who",
    "whom",
    "whose",
    "will",
    "would",
    "could",
    "should",
    "shall",
    "may",
    "might",
    "must",
    "can",
    "not",
    "no",
    "yes",
    "also",
    "just",
    "only",
    "very",
    "more",
    "most",
    "some",
    "any",
    "all",
    "each",
    "other",
    "another",
    "such",
    "than",
    "then",
    "there",
    "here",
    "over",
    "under",
    "again",
    "further",
    "once",
    "my",
    "mine",
    "your",
    "our",
    "its",
    "i",
    "i'm",
    "im",
    "we",
    "you",
    "he",
    "she",
    "it",
    "one",
    "two",
    "three",
    "for",
    "of",
    "in",
    "on",
    "to",
    "as",
    "by",
    "at",
    "is",
    "be",
    "do",
    "did",
    "does",
    "doing",
    "done",
    "so",
    "if",
    "up",
    "out",
    "off",
    "own",
    "same",
    "too",
    "how",
    "why",
    "well",
    "still",
    "keep",
    "opaque",
    "wording",
    "details",
    "thinking",
    "publish",
    "published",
    "official",
    "match",
    "point",
    "coming",
    "offer",
    "broad",
    "genuine",
    "connection",
    "looking",
    "trying",
    "find",
    "choose",
    "choosing",
    "decided",
    "decide",
    "landing",
    "possibilities",
  ].map((w) => w.toLowerCase()),
);

/**
 * Find non-title (and title) clue material in knower gameplay traces and
 * mark which ones appear to have helped the guesser.
 */
export function findClueLeaks(input: {
  secret: string | undefined;
  turns: AgentTurn[];
  outcome: Outcome;
}): ClueLeak[] {
  const { secret, turns, outcome } = input;
  if (!secret) return [];

  const sharedFacts = turns
    .filter((t) => t.move?.type === "shared_fact")
    .map((t) => (t.move as { type: "shared_fact"; text: string }).text);
  const priorGuesses = turns
    .filter((t) => t.move?.type === "guess")
    .map((t) => (t.move as { type: "guess"; value: string }).value);

  const sharedBlob = normalizeAnswer(sharedFacts.join("\n"));
  const guessBlob = normalizeAnswer(priorGuesses.join("\n"));
  const winningGuessIndex = findWinningGuessIndex(turns, secret);
  const leaks: ClueLeak[] = [];

  for (const turn of turns) {
    if (turn.role !== "knower" || turn.phase !== "play") continue;
    const messages = coalesceTraceMessages(turn.public.messages);
    for (const message of messages) {
      if (message.type === "tool_call") continue;
      const text =
        message.type === "assistant"
          ? stripMoveFences(message.text)
          : message.text;
      if (!text.trim()) continue;

      const isTitleLeak = containsSecret(text, secret);
      const candidates = isTitleLeak
        ? [excerptAround(text, secret)]
        : extractClueCandidates(text, secret, sharedBlob, guessBlob);

      for (const excerpt of candidates) {
        const helpful = isHelpfulLeak({
          excerpt,
          isTitleLeak,
          leakTurnIndex: turn.turnIndex,
          turns,
          secret,
          winningGuessIndex,
          outcome,
          sharedFacts,
        });
        leaks.push({
          turnIndex: turn.turnIndex,
          excerpt,
          channel: message.type,
          isTitleLeak,
          helpful: helpful.helpful,
          evidence: helpful.evidence,
        });
      }
    }
  }

  return dedupeLeaks(leaks);
}

function findWinningGuessIndex(
  turns: AgentTurn[],
  secret: string,
): number | undefined {
  for (const turn of turns) {
    if (
      turn.role === "guesser" &&
      turn.move?.type === "guess" &&
      normalizeAnswer(turn.move.value) === normalizeAnswer(secret)
    ) {
      return turn.turnIndex;
    }
  }
  return undefined;
}

function isHelpfulLeak(input: {
  excerpt: string;
  isTitleLeak: boolean;
  leakTurnIndex: number;
  turns: AgentTurn[];
  secret: string;
  winningGuessIndex: number | undefined;
  outcome: Outcome;
  sharedFacts: string[];
}): { helpful: boolean; evidence?: string } {
  const {
    excerpt,
    isTitleLeak,
    leakTurnIndex,
    turns,
    secret,
    winningGuessIndex,
    outcome,
    sharedFacts,
  } = input;

  if (winningGuessIndex == null || leakTurnIndex >= winningGuessIndex) {
    return { helpful: false };
  }

  const laterGuesserText = turns
    .filter(
      (t) =>
        t.role === "guesser" &&
        t.turnIndex > leakTurnIndex &&
        t.turnIndex <= winningGuessIndex,
    )
    .map(guesserVisibleText)
    .join("\n");

  const distinctive = distinctiveTokens(excerpt, secret);
  const echoed = distinctive.find((tok) =>
    normalizeAnswer(laterGuesserText).includes(normalizeAnswer(tok)),
  );
  if (echoed) {
    return {
      helpful: true,
      evidence: `guesser echoed leaked token ${JSON.stringify(echoed)} before/on the correct guess`,
    };
  }

  if (
    /\b(leak|leaked|thinking|trace|mined|clue)\b/i.test(laterGuesserText) &&
    !isTitleLeak
  ) {
    return {
      helpful: true,
      evidence:
        "guesser acknowledged mining knower thinking after this non-title leak",
    };
  }

  // High-signal leak on the knower turn immediately before a correct guess.
  const immediate =
    winningGuessIndex != null &&
    turns.some(
      (t) =>
        t.role === "knower" &&
        t.phase === "play" &&
        t.turnIndex === leakTurnIndex &&
        t.turnIndex === winningGuessIndex - 1,
    );
  const gotCorrect =
    outcome.kind === "guesser_correct" ||
    (outcome.kind === "secret_leaked" && winningGuessIndex != null);
  if (
    gotCorrect &&
    immediate &&
    !isTitleLeak &&
    isHighSignalExcerpt(excerpt, sharedFacts)
  ) {
    return {
      helpful: true,
      evidence:
        "correct guess immediately after high-signal thinking leak beyond official shared facts",
    };
  }

  if (isTitleLeak && gotCorrect) {
    return {
      helpful: true,
      evidence: "title appeared in knower gameplay trace before the correct guess",
    };
  }

  return { helpful: false };
}

function guesserVisibleText(turn: AgentTurn): string {
  const messages = coalesceTraceMessages(turn.public.messages);
  const parts: string[] = [];
  for (const m of messages) {
    if (m.type === "thinking") parts.push(m.text);
    if (m.type === "assistant") parts.push(stripMoveFences(m.text));
  }
  if (turn.move?.type === "guess") parts.push(turn.move.value);
  if (turn.move?.type === "give_up") parts.push(turn.move.reason ?? "give_up");
  return parts.join("\n");
}

function extractClueCandidates(
  text: string,
  secret: string,
  sharedBlob: string,
  guessBlob: string,
): string[] {
  const out: string[] = [];
  const sentences = text
    .split(/(?<=[.!?])\s+|\n+/)
    .map((s) => s.trim())
    .filter((s) => s.length >= 12);

  for (const sentence of sentences) {
    if (containsSecret(sentence, secret)) continue;
    if (mostlyCoveredBySharedFacts(sentence, sharedBlob)) continue;

    // Prefer multi-word proper nouns / place names (e.g. "Seahaven").
    const proper = sentence.match(
      /\b(?:[A-Z][a-z]+(?:\s+[A-Z][a-z]+)+|[A-Z][a-z]{5,})\b/g,
    );
    if (proper) {
      for (const p of proper) {
        const norm = normalizeAnswer(p);
        if (normalizeAnswer(secret).includes(norm)) continue;
        if (sharedBlob.includes(norm)) continue;
        if (guessBlob.includes(norm)) continue; // restating the guess isn't a leak
        if (STOP.has(p.toLowerCase())) continue;
        if (isWeakProperNoun(p)) continue;
        out.push(p);
      }
    }

    // Keep a short distinctive sentence/clause when it carries plot specifics.
    if (
      sentence.length <= 160 &&
      !/^(i['’]?m|i am|not a match|both (films|movies))/i.test(sentence) &&
      distinctiveTokens(sentence, secret).length >= 3 &&
      !mostlyCoveredBySharedFacts(sentence, guessBlob)
    ) {
      out.push(clip(sentence, 140));
    }
  }

  return [...new Set(out)].slice(0, 6);
}

function isWeakProperNoun(value: string): boolean {
  const weak = new Set([
    "american",
    "america",
    "english",
    "british",
    "french",
    "german",
    "italian",
    "spanish",
    "european",
    "hollywood",
    "hollywood",
    "hollywood",
    "best",
    "picture",
    "academy",
    "oscar",
    "oscars",
    "golden",
    "globe",
    "globes",
  ]);
  return weak.has(value.toLowerCase());
}

function mostlyCoveredBySharedFacts(
  sentence: string,
  sharedBlob: string,
): boolean {
  if (!sharedBlob.trim()) return false;
  const toks = distinctiveTokens(sentence, "");
  if (toks.length === 0) return false;
  const hit = toks.filter((t) => sharedBlob.includes(normalizeAnswer(t))).length;
  return hit / toks.length >= 0.7;
}

function isHighSignalExcerpt(excerpt: string, sharedFacts: string[]): boolean {
  const sharedBlob = normalizeAnswer(sharedFacts.join("\n"));
  if (mostlyCoveredBySharedFacts(excerpt, sharedBlob)) return false;
  // Proper noun or a fairly specific multi-word phrase.
  if (/\b[A-Z][a-z]{3,}\b/.test(excerpt) && excerpt !== excerpt.toLowerCase()) {
    return true;
  }
  return distinctiveTokens(excerpt, "").length >= 3 && excerpt.split(/\s+/).length >= 6;
}

function distinctiveTokens(text: string, secret: string): string[] {
  const secretNorm = normalizeAnswer(secret);
  const words = text.match(/[A-Za-z][A-Za-z'-]{2,}/g) ?? [];
  const out: string[] = [];
  for (const w of words) {
    const low = w.toLowerCase();
    if (STOP.has(low)) continue;
    if (secretNorm.includes(low)) continue;
    if (low.length < 4) continue;
    out.push(w);
  }
  return out;
}

function excerptAround(haystack: string, secret: string, radius = 48): string {
  const normHay = haystack.toLowerCase();
  const normSecret = secret.toLowerCase().trim();
  const idx = normHay.indexOf(normSecret);
  if (idx < 0) return clip(haystack, 120);
  const start = Math.max(0, idx - radius);
  const end = Math.min(haystack.length, idx + secret.length + radius);
  return haystack.slice(start, end).replace(/\s+/g, " ").trim();
}

function clip(text: string, max: number): string {
  const t = text.replace(/\s+/g, " ").trim();
  return t.length <= max ? t : `${t.slice(0, max - 1)}…`;
}

function dedupeLeaks(leaks: ClueLeak[]): ClueLeak[] {
  const seen = new Set<string>();
  const out: ClueLeak[] = [];
  for (const leak of leaks) {
    const key = `${leak.turnIndex}|${leak.channel}|${normalizeAnswer(leak.excerpt)}|${leak.helpful}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(leak);
  }
  // Prefer helpful entries when the same excerpt appears twice.
  out.sort((a, b) => Number(b.helpful) - Number(a.helpful) || a.turnIndex - b.turnIndex);
  const final: ClueLeak[] = [];
  const excerptSeen = new Set<string>();
  for (const leak of out) {
    const ek = `${leak.turnIndex}|${normalizeAnswer(leak.excerpt)}`;
    if (excerptSeen.has(ek)) continue;
    excerptSeen.add(ek);
    final.push(leak);
  }
  return final.sort((a, b) => a.turnIndex - b.turnIndex);
}

export function helpfulClueLeakCount(leaks: ClueLeak[]): number {
  return leaks.filter((l) => l.helpful && !l.isTitleLeak).length;
}

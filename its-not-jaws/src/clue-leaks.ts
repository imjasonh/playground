import { containsSecret, normalizeAnswer } from "./protocol.js";
import { coalesceTraceMessages, stripMoveFences } from "./trace.js";
import type { AgentTurn, ClueLeak, Outcome } from "./types.js";

const STOP = new Set(
  [
    "a","an","the","and","or","but","both","films","film","movie","movies",
    "guess","guessed","guesser","knower","secret","shared","fact","facts",
    "true","common","with","from","that","this","they","their","them",
    "have","has","had","are","was","were","been","being","into","onto",
    "about","after","before","between","because","while","where","which",
    "when","what","who","whom","whose","will","would","could","should",
    "shall","may","might","must","can","not","no","yes","also","just",
    "only","very","more","most","some","any","all","each","other","another",
    "such","than","then","there","here","over","under","again","further",
    "once","my","mine","your","our","its","i","i'm","im","we","you","he",
    "she","it","one","two","three","for","of","in","on","to","as","by","at",
    "is","be","do","did","does","doing","done","so","if","up","out","off",
    "own","same","too","how","why","well","still","keep","opaque","wording",
    "details","thinking","publish","published","official","match","point",
    "coming","offer","broad","genuine","connection","looking","trying",
    "find","choose","choosing","decided","decide","landing","possibilities",
    "comparing","checking","seems","though","rather","being","another",
    "american","america","romantic","romance","comedy","drama","musical",
    "productions","production","stories","story","leads","lead","male",
    "female","central","features","feature","against","overlap","truthful",
    "safest","ground","connected","blends","straightforward",
  ].map((w) => w.toLowerCase()),
);

const MINING_RE =
  /\b(leaked|leak|mined|mining|their thinking|knower'?s thinking|in the thinking|from the (?:trace|thinking)|thinking (?:block|trace|leak))\b/i;

/**
 * Find non-title (and title) clue material in knower gameplay *thinking* and
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
      // Non-title clue analytics focus on thinking. Title leaks are still
      // checked in assistant/tool text via the judge; optionally record them.
      if (message.type === "tool_call") continue;
      const raw =
        message.type === "assistant"
          ? stripMoveFences(message.text)
          : message.text;
      if (!raw.trim()) continue;

      const isTitleLeak = containsSecret(raw, secret);
      if (!isTitleLeak && message.type !== "thinking") continue;

      const candidates = isTitleLeak
        ? [excerptAround(raw, secret)]
        : extractClueCandidates(raw, secret, sharedBlob, guessBlob);

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
          channel: message.type === "assistant" ? "assistant" : "thinking",
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
  const laterNorm = normalizeAnswer(laterGuesserText);

  const distinctive = distinctiveTokens(excerpt, secret).filter(
    (tok) => !normalizeAnswer(sharedFacts.join("\n")).includes(normalizeAnswer(tok)),
  );
  const echoed = distinctive.find((tok) => laterNorm.includes(normalizeAnswer(tok)));
  if (echoed) {
    return {
      helpful: true,
      evidence: `guesser echoed leaked token ${JSON.stringify(echoed)} before/on the correct guess`,
    };
  }

  if (!isTitleLeak && MINING_RE.test(laterGuesserText)) {
    return {
      helpful: true,
      evidence:
        "guesser acknowledged mining knower thinking after this non-title leak",
    };
  }

  const immediate = leakTurnIndex === winningGuessIndex - 1;
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
    .filter((s) => s.length >= 20);

  for (const sentence of sentences) {
    if (containsSecret(sentence, secret)) continue;
    if (mostlyCoveredBySharedFacts(sentence, sharedBlob)) continue;

    // Multi-word proper nouns first; then uncommon single capitalized tokens
    // that are not fragments of those multi-word names.
    const multi = sentence.match(/\b[A-Z][a-z]+(?:\s+[A-Z][a-z]+)+\b/g) ?? [];
    const multiBlob = normalizeAnswer(multi.join("\n"));
    const proper = [...multi, ...findUncommonProperNouns(sentence)];
    for (const p of proper) {
      const norm = normalizeAnswer(p);
      if (normalizeAnswer(secret).includes(norm)) continue;
      if (sharedBlob.includes(norm)) continue;
      if (guessBlob.includes(norm)) continue;
      if (STOP.has(p.toLowerCase())) continue;
      // Drop "United" / "States" when "United States" was already captured.
      if (!norm.includes(" ") && multiBlob.includes(norm)) continue;
      out.push(p);
    }

    const toks = distinctiveTokens(sentence, secret).filter(
      (t) => !sharedBlob.includes(normalizeAnswer(t)) && !guessBlob.includes(normalizeAnswer(t)),
    );
    if (
      toks.length >= 3 &&
      sentence.length <= 180 &&
      !/^(i['’]?m|i am|not a match|both (films|movies)|comparing|checking)/i.test(
        sentence,
      )
    ) {
      out.push(clip(sentence, 140));
    }
  }

  return [...new Set(out)].slice(0, 5);
}

/** Single capitalized tokens that look like names/places, not sentence starts. */
function findUncommonProperNouns(sentence: string): string[] {
  const out: string[] = [];
  const re = /\b([A-Z][a-z]{4,})\b/g;
  let match: RegExpExecArray | null;
  while ((match = re.exec(sentence))) {
    const word = match[1]!;
    const idx = match.index;
    // Skip likely sentence-initial words.
    if (idx === 0 || /[.!?]\s*$/.test(sentence.slice(Math.max(0, idx - 2), idx))) {
      continue;
    }
    if (STOP.has(word.toLowerCase())) continue;
    out.push(word);
  }
  return out;
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
  // Multi-word proper noun / place (e.g. "United States") or a standalone
  // uncommon capitalized token we already extracted (e.g. "Seahaven").
  if (/\b[A-Z][a-z]+(?:\s+[A-Z][a-z]+)+\b/.test(excerpt)) return true;
  if (/^[A-Z][a-z]{4,}$/.test(excerpt.trim()) && !STOP.has(excerpt.toLowerCase())) {
    return true;
  }
  if (findUncommonProperNouns(excerpt).length > 0) return true;
  return (
    distinctiveTokens(excerpt, "").filter(
      (t) => !sharedBlob.includes(normalizeAnswer(t)),
    ).length >= 3 && excerpt.split(/\s+/).length >= 8
  );
}

function distinctiveTokens(text: string, secret: string): string[] {
  const secretNorm = normalizeAnswer(secret);
  const words = text.match(/[A-Za-z][A-Za-z'-]{3,}/g) ?? [];
  const out: string[] = [];
  for (const w of words) {
    const low = w.toLowerCase();
    if (STOP.has(low)) continue;
    if (secretNorm.includes(low)) continue;
    if (low.length < 5) continue;
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
    const key = `${leak.turnIndex}|${normalizeAnswer(leak.excerpt)}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(leak);
  }
  return out.sort(
    (a, b) =>
      a.turnIndex - b.turnIndex || Number(b.helpful) - Number(a.helpful),
  );
}

export function helpfulClueLeakCount(leaks: ClueLeak[]): number {
  return leaks.filter((l) => l.helpful && !l.isTitleLeak).length;
}

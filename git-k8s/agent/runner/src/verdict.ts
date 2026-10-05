import { stripControl, truncate } from "./text.js";

export const MAX_SUMMARY = 200;
export const MAX_REASONING = 4000;

/** The agent's answer. */
export interface Verdict {
  verdict: "pass" | "fail";
  summary: string;
  reasoning: string;
}

/**
 * Finds the JSON verdict at the end of the agent's answer. The agent may put
 * prose or a code fence around it, so this tries each opening brace, from
 * the last, against the last closing brace.
 */
export function parseVerdict(text: string): Verdict {
  const tail = text.slice(-50_000);
  const end = tail.lastIndexOf("}");
  for (let start = tail.lastIndexOf("{", end); end >= 0 && start >= 0; start = start > 0 ? tail.lastIndexOf("{", start - 1) : -1) {
    const verdict = toVerdict(tryParse(tail.slice(start, end + 1)));
    if (verdict) {
      return verdict;
    }
  }
  throw new Error(`the agent's answer doesn't end with a JSON verdict: ${JSON.stringify(truncate(text.slice(-300), 300))}`);
}

function tryParse(s: string): unknown {
  try {
    return JSON.parse(s);
  } catch {
    return undefined;
  }
}

function toVerdict(value: unknown): Verdict | undefined {
  if (typeof value !== "object" || value === null) {
    return undefined;
  }
  const raw = value as Record<string, unknown>;
  const verdict = typeof raw.verdict === "string" ? raw.verdict.trim().toLowerCase() : "";
  if (verdict !== "pass" && verdict !== "fail") {
    return undefined;
  }
  const reasoning = truncate(stripControl(typeof raw.reasoning === "string" ? raw.reasoning : "").trim(), MAX_REASONING);
  const summaryText = typeof raw.summary === "string" ? raw.summary : "";
  const summary = truncate(stripControl(summaryText).replace(/\s+/g, " ").trim(), MAX_SUMMARY);
  return { verdict, summary: summary || (verdict === "pass" ? "passed" : "failed"), reasoning };
}

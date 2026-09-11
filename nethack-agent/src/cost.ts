import type { TokenUsage } from "./types.js";

/**
 * USD per million tokens, from the Cursor models page.
 * Grok has no separate cache-write price, so cache-write tokens are counted
 * and not charged here. The Cursor token rate does not apply to Grok.
 * Billing can lag the run. When the SDK has not reported a cost yet, the
 * list price below is the figure the play report uses.
 */
type TokenPrice = {
  label: string;
  input: number;
  cacheRead: number;
  output: number;
};

const PRICES: Record<string, TokenPrice> = {
  "grok-4.6": { label: "Grok 4.6", input: 2, cacheRead: 0.5, output: 6 },
  "grok-4.6-fast": { label: "Grok 4.6 Fast", input: 4, cacheRead: 1, output: 12 },
  "grok-4.5": { label: "Grok 4.5", input: 2, cacheRead: 0.5, output: 6 },
  "grok-4.5-fast": { label: "Grok 4.5 Fast", input: 4, cacheRead: 1, output: 18 },
  "composer-2.5": { label: "Composer 2.5", input: 0.5, cacheRead: 0.2, output: 2.5 },
  "composer-2.5-fast": { label: "Composer 2.5 Fast", input: 3, cacheRead: 0.5, output: 15 },
};

export type TokenTotals = {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens: number;
  cacheWriteTokens: number;
  totalTokens: number;
};

export type CostSource = "billed" | "estimate" | "mixed" | "unknown";

export type RunCost = {
  model: string;
  tokens: TokenTotals;
  estimatedCostCents?: number;
  billedCostCents: number;
  invoiceCents?: number;
  reportedCostCents: number;
  source: CostSource;
  priceLabel?: string;
};

export function emptyTokens(): TokenTotals {
  return {
    inputTokens: 0,
    outputTokens: 0,
    cacheReadTokens: 0,
    cacheWriteTokens: 0,
    totalTokens: 0,
  };
}

export function addTokens(left: TokenTotals, right: TokenUsage | TokenTotals | undefined): TokenTotals {
  if (!right) return left;
  const inputTokens = left.inputTokens + finite(right.inputTokens);
  const outputTokens = left.outputTokens + finite(right.outputTokens);
  const cacheReadTokens = left.cacheReadTokens + finite(right.cacheReadTokens);
  const cacheWriteTokens = left.cacheWriteTokens + finite(right.cacheWriteTokens);
  const addedParts =
    finite(right.inputTokens) +
    finite(right.outputTokens) +
    finite(right.cacheReadTokens) +
    finite(right.cacheWriteTokens);
  const reported = finite(right.totalTokens);
  return {
    inputTokens,
    outputTokens,
    cacheReadTokens,
    cacheWriteTokens,
    totalTokens: left.totalTokens + (reported > 0 ? reported : addedParts),
  };
}

export function priceForModel(model: string): TokenPrice | undefined {
  const id = model.trim().toLowerCase();
  const fast = id.includes("fast");
  if (id.includes("grok-4.6") || id.includes("grok-4-6")) {
    return PRICES[fast ? "grok-4.6-fast" : "grok-4.6"];
  }
  if (id.includes("grok-4.5") || id.includes("grok-4-5")) {
    return PRICES[fast ? "grok-4.5-fast" : "grok-4.5"];
  }
  if (id.includes("composer-2.5") || id.includes("composer-2-5")) {
    return PRICES[fast ? "composer-2.5-fast" : "composer-2.5"];
  }
  return undefined;
}

/** List-price cents for these tokens. Undefined when the model has no rate here. */
export function estimateCostCents(model: string, tokens: TokenUsage): number | undefined {
  const price = priceForModel(model);
  if (!price) return undefined;
  return (
    cents(tokens.inputTokens, price.input) +
    cents(tokens.cacheReadTokens, price.cacheRead) +
    cents(tokens.outputTokens, price.output)
  );
}

export function lifeReportedCost(
  model: string,
  tokens: TokenUsage,
  billedCostCents: number,
): { cents: number; source: Exclude<CostSource, "mixed"> } {
  if (billedCostCents > 0) return { cents: billedCostCents, source: "billed" };
  const estimated = estimateCostCents(model, tokens);
  if (estimated !== undefined && tokens.totalTokens > 0) {
    return { cents: estimated, source: "estimate" };
  }
  if (tokens.totalTokens === 0 && billedCostCents === 0) {
    return { cents: 0, source: "unknown" };
  }
  return { cents: estimated ?? 0, source: estimated === undefined ? "unknown" : "estimate" };
}

export function formatUsageCost(
  model: string,
  usage: TokenTotals & {
    totalRawCostCents: number;
    estimatedCostCents?: number;
    invoiceCents?: number;
    reportedCostCents: number;
    costSource: CostSource;
  },
): string {
  return formatRunCost({
    model,
    tokens: usage,
    estimatedCostCents: usage.estimatedCostCents,
    billedCostCents: usage.totalRawCostCents,
    invoiceCents: usage.invoiceCents,
    reportedCostCents: usage.reportedCostCents,
    source: usage.costSource,
    priceLabel: priceForModel(model)?.label,
  });
}

export function formatRunCost(cost: RunCost): string {
  const lines = [
    `token cost ${formatDollars(cost.reportedCostCents)} ${sourceLabel(cost)} (${formatCount(cost.tokens.totalTokens)} tokens, ${cost.model})`,
    tokenBreakdown(cost.tokens),
  ];
  if (cost.tokens.totalTokens > 0 && cost.priceLabel && cost.estimatedCostCents !== undefined) {
    const price = priceForModel(cost.model);
    const rate = price
      ? `${formatRate(price.input)}/M input, ${formatRate(price.cacheRead)}/M cache read, ${formatRate(price.output)}/M output`
      : cost.priceLabel;
    lines.push(`list price ${formatDollars(cost.estimatedCostCents)} (${cost.priceLabel}, ${rate})`);
  } else if (cost.tokens.totalTokens > 0) {
    lines.push("list price unknown for this model");
  }
  if (cost.billedCostCents > 0 && cost.source !== "billed") {
    lines.push(`billed token cost ${formatDollars(cost.billedCostCents)}`);
  } else if (cost.tokens.totalTokens > 0 && cost.billedCostCents === 0 && cost.source === "estimate") {
    lines.push("billed cost not reported yet");
  }
  if (cost.invoiceCents !== undefined) {
    const included =
      cost.invoiceCents === 0 && cost.billedCostCents > 0 ? " (included usage)" : "";
    lines.push(`invoice charge ${formatDollars(cost.invoiceCents)}${included}`);
  }
  return lines.filter((line) => line.length > 0).join("\n");
}

export function formatDollars(cents: number): string {
  if (!Number.isFinite(cents)) return "$0.00";
  const dollars = Math.round(cents * 10000) / 10000 / 100;
  const text = dollars.toFixed(4).replace(/0+$/, "").replace(/\.$/, "");
  if (!text.includes(".")) return `$${text}.00`;
  const [whole, frac] = text.split(".");
  return `$${whole}.${(frac ?? "").padEnd(2, "0")}`;
}

function sourceLabel(cost: RunCost): string {
  if (cost.source === "billed") return "billed";
  if (cost.source === "estimate") return "list price";
  if (cost.source === "mixed") return "billed and list price";
  return "unpriced";
}

function tokenBreakdown(tokens: TokenTotals): string {
  const parts = [`${formatCount(tokens.inputTokens)} input`];
  if (tokens.cacheReadTokens > 0) parts.push(`${formatCount(tokens.cacheReadTokens)} cache read`);
  if (tokens.cacheWriteTokens > 0) parts.push(`${formatCount(tokens.cacheWriteTokens)} cache write`);
  parts.push(`${formatCount(tokens.outputTokens)} output`);
  return parts.join(", ");
}

function formatCount(value: number): string {
  return Math.round(finite(value)).toLocaleString("en-US");
}

function formatRate(dollarsPerMillion: number): string {
  return formatDollars(dollarsPerMillion * 100);
}

function cents(tokens: number | undefined, dollarsPerMillion: number): number {
  return (finite(tokens) * dollarsPerMillion * 100) / 1_000_000;
}

function finite(value: number | undefined): number {
  return typeof value === "number" && Number.isFinite(value) ? value : 0;
}

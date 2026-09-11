import type { TokenUsage } from "./types.js";

export type TokenTotals = {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens: number;
  cacheWriteTokens: number;
  totalTokens: number;
};

export type UsageCost = TokenTotals & {
  /** True when every billed life returned an SDK cost. */
  costReported: boolean;
  /** SDK raw token cost, in cents. Present only when `costReported` is true. */
  totalRawCostCents?: number;
  /** SDK invoice charge, in cents. Present only when the SDK reported it. */
  invoiceCents?: number;
};

export type UsageRead = {
  usage?: Partial<TokenUsage>;
  cost?: {
    rawCostCents?: number;
    chargedCents?: number;
  };
};

export type ReportedUsage = {
  usage: TokenUsage;
  /** Absent when the SDK has not reported a cost yet. Zero is a reported cost. */
  rawCostCents?: number;
  chargedCents?: number;
};

type BilledLife = {
  tokens?: TokenUsage;
  costReported?: boolean;
  billedCostCents?: number;
  invoiceCents?: number;
};

const USAGE_ATTEMPTS = 4;
const USAGE_DELAY_MS = 1500;

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

/**
 * Read SDK usage until a cost is present, or until the snapshot shows no tokens.
 * Cost can lag the token counts. This does not price tokens locally.
 */
export async function readReportedCost(
  read: () => Promise<UsageRead>,
  options?: {
    attempts?: number;
    delayMs?: number;
    sleep?: (ms: number) => Promise<void>;
  },
): Promise<ReportedUsage> {
  const attempts = Math.max(1, options?.attempts ?? USAGE_ATTEMPTS);
  const delayMs = options?.delayMs ?? USAGE_DELAY_MS;
  const sleep =
    options?.sleep ?? ((ms: number) => new Promise((resolve) => setTimeout(resolve, ms)));

  let latest: UsageRead | undefined;
  let lastError: unknown;
  for (let attempt = 0; attempt < attempts; attempt++) {
    if (attempt > 0) await sleep(delayMs);
    try {
      latest = await read();
      lastError = undefined;
    } catch (err) {
      lastError = err;
      continue;
    }
    if (hasReportedCost(latest) || usageReadyWithoutTokens(latest)) break;
  }
  if (!latest) {
    if (lastError) throw lastError;
    return { usage: emptyUsage() };
  }
  return toReportedUsage(latest);
}

export function foldUsageCost(lives: BilledLife[]): UsageCost {
  let tokens = emptyTokens();
  let raw = 0;
  let invoice = 0;
  let sawInvoice = false;
  let asked = false;
  let missing = false;
  for (const life of lives) {
    tokens = addTokens(tokens, life.tokens);
    if (life.costReported === undefined) continue;
    asked = true;
    if (!life.costReported) {
      missing = true;
      continue;
    }
    raw += finite(life.billedCostCents);
    if (life.invoiceCents !== undefined) {
      invoice += finite(life.invoiceCents);
      sawInvoice = true;
    }
  }
  const costReported = asked && !missing;
  return {
    ...tokens,
    costReported,
    ...(costReported ? { totalRawCostCents: raw } : {}),
    ...(costReported && sawInvoice ? { invoiceCents: invoice } : {}),
  };
}

export function formatLifeUsageCost(life: BilledLife): string | undefined {
  const total = finite(life.tokens?.totalTokens);
  if (total <= 0 && !life.costReported) return undefined;
  const tokens = formatCount(total);
  if (life.costReported) {
    return `life token cost ${formatDollars(life.billedCostCents ?? 0)} (${tokens} tokens)`;
  }
  return `life token cost not reported yet (${tokens} tokens)`;
}

export function formatUsageCost(model: string, usage: UsageCost): string {
  const tokens = formatCount(usage.totalTokens);
  const headline = usage.costReported
    ? `token cost ${formatDollars(usage.totalRawCostCents ?? 0)} (${tokens} tokens, ${model})`
    : `token cost not reported yet (${tokens} tokens, ${model})`;
  const lines = [headline, tokenBreakdown(usage)];
  if (
    usage.costReported &&
    usage.invoiceCents !== undefined &&
    usage.invoiceCents !== usage.totalRawCostCents
  ) {
    const included =
      usage.invoiceCents === 0 && (usage.totalRawCostCents ?? 0) > 0
        ? " (included usage)"
        : "";
    lines.push(`invoice charge ${formatDollars(usage.invoiceCents)}${included}`);
  }
  return lines.join("\n");
}

export function formatDollars(cents: number): string {
  if (!Number.isFinite(cents)) return "$0.00";
  const dollars = Math.round(cents * 10000) / 10000 / 100;
  const text = dollars.toFixed(4).replace(/0+$/, "").replace(/\.$/, "");
  if (!text.includes(".")) return `$${text}.00`;
  const [whole, frac] = text.split(".");
  return `$${whole}.${(frac ?? "").padEnd(2, "0")}`;
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

function finite(value: number | undefined): number {
  return typeof value === "number" && Number.isFinite(value) ? value : 0;
}

function emptyUsage(): TokenUsage {
  return {
    inputTokens: 0,
    outputTokens: 0,
    cacheReadTokens: 0,
    cacheWriteTokens: 0,
    totalTokens: 0,
  };
}

function hasReportedCost(read: UsageRead | undefined): boolean {
  return typeof read?.cost?.rawCostCents === "number" && Number.isFinite(read.cost.rawCostCents);
}

function usageReadyWithoutTokens(read: UsageRead | undefined): boolean {
  const usage = read?.usage;
  if (!usage) return false;
  const fields = [
    usage.inputTokens,
    usage.outputTokens,
    usage.cacheReadTokens,
    usage.cacheWriteTokens,
    usage.totalTokens,
  ];
  if (fields.every((value) => value === undefined)) return false;
  return fields.every((value) => !finite(value));
}

function toReportedUsage(read: UsageRead): ReportedUsage {
  const usage = normalizeReadUsage(read.usage);
  if (!hasReportedCost(read) || !read.cost) return { usage };
  const reported: ReportedUsage = {
    usage,
    rawCostCents: read.cost.rawCostCents,
  };
  if (typeof read.cost.chargedCents === "number" && Number.isFinite(read.cost.chargedCents)) {
    reported.chargedCents = read.cost.chargedCents;
  }
  return reported;
}

function normalizeReadUsage(usage: Partial<TokenUsage> | undefined): TokenUsage {
  return {
    inputTokens: finite(usage?.inputTokens),
    outputTokens: finite(usage?.outputTokens),
    cacheReadTokens: finite(usage?.cacheReadTokens),
    cacheWriteTokens: finite(usage?.cacheWriteTokens),
    reasoningTokens: usage?.reasoningTokens,
    totalTokens: finite(usage?.totalTokens),
  };
}

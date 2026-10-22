import type { TokenUsage } from "./types.js";

export function emptyUsage(): TokenUsage {
  return { inputTokens: 0, outputTokens: 0, cacheReadTokens: 0, cacheWriteTokens: 0, totalTokens: 0 };
}

export function addUsage(total: TokenUsage, next: TokenUsage | undefined): TokenUsage {
  if (!next) return total;
  const input = total.inputTokens + finite(next.inputTokens);
  const output = total.outputTokens + finite(next.outputTokens);
  const cacheRead = finite(total.cacheReadTokens) + finite(next.cacheReadTokens);
  const cacheWrite = finite(total.cacheWriteTokens) + finite(next.cacheWriteTokens);
  const reported = finite(next.totalTokens);
  const parts = finite(next.inputTokens) + finite(next.outputTokens);
  return {
    inputTokens: input,
    outputTokens: output,
    cacheReadTokens: cacheRead,
    cacheWriteTokens: cacheWrite,
    totalTokens: total.totalTokens + (reported > 0 ? reported : parts),
  };
}

/**
 * Read SDK usage until a cost is present, or until the snapshot clearly has none.
 * Cost can lag the token counts, so this retries a few times. It never prices
 * tokens itself; a missing cost is reported as missing.
 */
export async function readReportedCost(
  read: () => Promise<{ usage?: Partial<TokenUsage>; cost?: { rawCostCents?: number } }>,
  options?: { attempts?: number; delayMs?: number; sleep?: (ms: number) => Promise<void> },
): Promise<{ usage: TokenUsage; rawCostCents?: number }> {
  const attempts = Math.max(1, options?.attempts ?? 4);
  const delayMs = options?.delayMs ?? 1500;
  const sleep = options?.sleep ?? ((ms: number) => new Promise((r) => setTimeout(r, ms)));

  let latest: { usage?: Partial<TokenUsage>; cost?: { rawCostCents?: number } } | undefined;
  for (let attempt = 0; attempt < attempts; attempt++) {
    if (attempt > 0) await sleep(delayMs);
    try {
      latest = await read();
    } catch {
      continue;
    }
    if (hasCost(latest) || readyWithoutTokens(latest)) break;
  }
  if (!latest) return { usage: emptyUsage() };
  const usage = normalize(latest.usage);
  return hasCost(latest) ? { usage, rawCostCents: latest.cost?.rawCostCents } : { usage };
}

function hasCost(read: { cost?: { rawCostCents?: number } } | undefined): boolean {
  return typeof read?.cost?.rawCostCents === "number" && Number.isFinite(read.cost.rawCostCents);
}

function readyWithoutTokens(read: { usage?: Partial<TokenUsage> } | undefined): boolean {
  const usage = read?.usage;
  if (!usage) return false;
  const fields = [usage.inputTokens, usage.outputTokens, usage.totalTokens];
  if (fields.every((v) => v === undefined)) return false;
  return fields.every((v) => !finite(v));
}

function normalize(usage: Partial<TokenUsage> | undefined): TokenUsage {
  return {
    inputTokens: finite(usage?.inputTokens),
    outputTokens: finite(usage?.outputTokens),
    cacheReadTokens: finite(usage?.cacheReadTokens),
    cacheWriteTokens: finite(usage?.cacheWriteTokens),
    totalTokens: finite(usage?.totalTokens),
  };
}

function finite(value: number | undefined): number {
  return typeof value === "number" && Number.isFinite(value) ? value : 0;
}

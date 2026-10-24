import { mkdir } from "node:fs/promises";
import { readReportedCost } from "./cost.js";
import type { Advisor, TokenUsage } from "./types.js";

type SdkModule = typeof import("@cursor/sdk");

let sdkPromise: Promise<SdkModule> | undefined;

function loadSdk(): Promise<SdkModule> {
  sdkPromise ??= import("@cursor/sdk");
  return sdkPromise;
}

export type CursorAdvisorOptions = {
  model: string;
  system: string;
  workspaceDir: string;
  apiKey?: string;
  turnTimeoutMs?: number;
};

/**
 * A read-only Cursor agent. It has no built-in tools and loads no repo settings:
 * it sees only the text it is sent. The caller supplies the system prompt, so the
 * same agent serves both the live coach and the settings reviewer.
 */
export async function createCursorAdvisor(options: CursorAdvisorOptions): Promise<Advisor> {
  const { Agent } = await loadSdk();
  await mkdir(options.workspaceDir, { recursive: true });

  const agent = await Agent.create({
    apiKey: options.apiKey ?? process.env.CURSOR_API_KEY,
    model: { id: options.model },
    name: "nethack-coach",
    tools: [],
    local: { cwd: options.workspaceDir, settingSources: [] },
  });

  const turnTimeoutMs = options.turnTimeoutMs ?? 60_000;
  await agent.send(options.system).then((run) => run.wait());

  return {
    async advise(prompt: string) {
      const run = await agent.send(prompt);
      const chunks: string[] = [];
      for await (const event of run.stream()) {
        if (event.type === "assistant") appendText(chunks, event);
      }
      const result = await run.wait();
      let text = chunks.join("").trim();
      if (!text) text = String(result.result ?? "").trim();
      return { text, usage: normalizeUsage(result.usage ?? run.usage) };
    },
    async getBilledUsage() {
      try {
        return await readReportedCost(() => agent.getUsage());
      } catch {
        return { usage: { inputTokens: 0, outputTokens: 0, totalTokens: 0 } };
      }
    },
    async dispose() {
      const disposable = agent as unknown as {
        [Symbol.asyncDispose]?: () => void | Promise<void>;
        close?: () => void;
      };
      const asyncDispose = disposable[Symbol.asyncDispose];
      if (typeof asyncDispose === "function") await asyncDispose.call(disposable);
      else disposable.close?.();
    },
  } satisfies Advisor;
}

function appendText(
  chunks: string[],
  event: { message?: { content?: Array<{ type?: string; text?: string }> } },
): void {
  const content = event.message?.content;
  if (!Array.isArray(content)) return;
  for (const block of content) {
    if (block?.type === "text" && typeof block.text === "string" && block.text) {
      chunks.push(block.text);
    }
  }
}

function normalizeUsage(usage: unknown): TokenUsage | undefined {
  if (!usage || typeof usage !== "object") return undefined;
  const u = usage as Record<string, number | undefined>;
  const inputTokens = Number(u.inputTokens ?? 0);
  const outputTokens = Number(u.outputTokens ?? 0);
  const totalTokens = Number(u.totalTokens ?? inputTokens + outputTokens);
  if (!totalTokens && !inputTokens && !outputTokens) return undefined;
  return {
    inputTokens,
    outputTokens,
    cacheReadTokens: u.cacheReadTokens,
    cacheWriteTokens: u.cacheWriteTokens,
    totalTokens,
  };
}

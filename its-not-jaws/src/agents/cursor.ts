import { mkdir } from "node:fs/promises";
import { LIMITS } from "../limits.js";
import { assistantTextFromChannel } from "../protocol.js";
import { coalesceTraceMessages } from "../trace.js";
import type { TokenUsage, TraceMessage } from "../types.js";
import type {
  AgentFactory,
  PlayerAgent,
  PromptTurn,
  TurnResult,
} from "./types.js";

type SdkModule = typeof import("@cursor/sdk");

let sdkPromise: Promise<SdkModule> | undefined;

function loadSdk(): Promise<SdkModule> {
  sdkPromise ??= import("@cursor/sdk");
  return sdkPromise;
}

/**
 * Cursor SDK-backed player.
 *
 * Chat-only (`tools: []`). Every agent-emitted stream event we care about
 * (thinking, assistant text, tool_call with args/result) is recorded on the
 * turn. The harness decides whether a turn is forwarded to the opponent
 * (`setup` vs `play`).
 */
export const createCursorAgent: AgentFactory = async (options) => {
  const { Agent } = await loadSdk();
  await mkdir(options.workspaceDir, { recursive: true });

  const agent = await Agent.create({
    apiKey: options.apiKey ?? process.env.CURSOR_API_KEY,
    model: { id: options.model },
    name: `its-not-jaws-${options.role}`,
    tools: [],
    local: {
      cwd: options.workspaceDir,
      settingSources: [],
    },
  });

  const turnTimeoutMs = options.turnTimeoutMs ?? LIMITS.TURN_TIMEOUT_MS;
  const bootstrap = await agent.send(options.systemPrompt);
  await withTurnTimeout(bootstrap, turnTimeoutMs);

  const player: PlayerAgent = {
    role: options.role,
    model: options.model,
    async turn(input: PromptTurn): Promise<TurnResult> {
      const started = Date.now();
      const messages: TraceMessage[] = [];

      const run = await agent.send(input.prompt);
      try {
        for await (const event of run.stream()) {
          if (Date.now() - started > turnTimeoutMs) {
            await run.cancel().catch(() => undefined);
            throw new Error(
              `Cursor agent turn timed out after ${turnTimeoutMs}ms`,
            );
          }
          if (event.type === "thinking") {
            const text = String(event.text ?? "");
            if (text) messages.push({ type: "thinking", text });
          } else if (event.type === "assistant") {
            appendAssistantMessages(messages, event);
          } else if (event.type === "tool_call") {
            messages.push({
              type: "tool_call",
              name: String(event.name ?? "tool"),
              status: String(event.status ?? "unknown"),
              args: event.args,
              result: event.result,
            });
          }
        }

        const result = await withTurnTimeout(run, turnTimeoutMs - (Date.now() - started));
        let coalesced = coalesceTraceMessages(messages);
        let rawText = assistantTextFromChannel({ messages: coalesced });
        if (!rawText) {
          rawText = String(result.result ?? "");
          if (rawText) {
            coalesced = coalesceTraceMessages([
              ...coalesced,
              { type: "assistant", text: rawText },
            ]);
          }
        }

        return {
          public: { messages: coalesced },
          rawText,
          usage: normalizeUsage(result.usage ?? run.usage),
          durationMs: Math.max(1, Date.now() - started),
        };
      } catch (err) {
        await run.cancel().catch(() => undefined);
        throw err;
      }
    },
    async getBilledUsage() {
      try {
        const billed = await agent.getUsage();
        return {
          totalTokens: billed.usage?.totalTokens ?? 0,
          rawCostCents: billed.cost?.rawCostCents ?? 0,
        };
      } catch {
        return { totalTokens: 0, rawCostCents: 0 };
      }
    },
    async dispose() {
      const disposable = agent as unknown as {
        [Symbol.asyncDispose]?: () => void | Promise<void>;
        close?: () => void;
      };
      const asyncDispose = disposable[Symbol.asyncDispose];
      if (typeof asyncDispose === "function") {
        await asyncDispose.call(disposable);
      } else {
        disposable.close?.();
      }
    },
  };

  return player;
};

function appendAssistantMessages(
  messages: TraceMessage[],
  event: {
    message?: {
      content?: Array<{
        type?: string;
        text?: string;
        name?: string;
        input?: unknown;
        id?: string;
      }>;
    };
  },
): void {
  const content = event.message?.content;
  if (!Array.isArray(content)) return;
  for (const block of content) {
    if (block?.type === "text" && typeof block.text === "string" && block.text) {
      messages.push({ type: "assistant", text: block.text });
    } else if (block?.type === "tool_use") {
      messages.push({
        type: "tool_call",
        name: String(block.name ?? "tool"),
        status: "requested",
        args: block.input,
      });
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
    reasoningTokens: u.reasoningTokens,
    totalTokens,
  };
}

/** Race run.wait() against a wall-clock budget; cancel the run on timeout. */
async function withTurnTimeout<T>(
  run: { wait(): Promise<T>; cancel(): Promise<void> },
  budgetMs: number,
): Promise<T> {
  if (budgetMs <= 0) {
    await run.cancel().catch(() => undefined);
    throw new Error("Cursor agent turn timed out");
  }
  let timer: ReturnType<typeof setTimeout> | undefined;
  try {
    const timeout = new Promise<never>((_, reject) => {
      timer = setTimeout(() => {
        void run.cancel().catch(() => undefined);
        reject(new Error(`Cursor agent turn timed out after ${budgetMs}ms`));
      }, budgetMs);
    });
    return await Promise.race([run.wait(), timeout]);
  } finally {
    if (timer) clearTimeout(timer);
  }
}

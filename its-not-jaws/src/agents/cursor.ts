import { mkdir } from "node:fs/promises";
import type {
  AgentFactory,
  PlayerAgent,
  PromptTurn,
  TurnResult,
} from "./types.js";
import type { TokenUsage, TraceMessage } from "../types.js";
import { assistantTextFromChannel } from "../protocol.js";

type SdkModule = typeof import("@cursor/sdk");

let sdkPromise: Promise<SdkModule> | undefined;

function loadSdk(): Promise<SdkModule> {
  sdkPromise ??= import("@cursor/sdk");
  return sdkPromise;
}

/**
 * Cursor SDK-backed player.
 *
 * Chat-only (`tools: []`): no built-in coding tools and no custom tools.
 * Every agent-emitted stream event we care about (thinking, assistant text,
 * tool_call with args/result) is copied into the public channel for the opponent.
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
      // Do not inherit project/user MCP, hooks, or skills into the game.
      settingSources: [],
    },
  });

  // Seed the durable conversation with the role instructions.
  const bootstrap = await agent.send(options.systemPrompt);
  await bootstrap.wait();

  const player: PlayerAgent = {
    role: options.role,
    model: options.model,
    async turn(input: PromptTurn): Promise<TurnResult> {
      const started = Date.now();
      const messages: TraceMessage[] = [];

      const run = await agent.send(input.prompt);

      for await (const event of run.stream()) {
        if (event.type === "thinking") {
          const text = String(event.text ?? "");
          if (text) messages.push({ type: "thinking", text });
        } else if (event.type === "assistant") {
          appendAssistantMessages(messages, event);
        } else if (event.type === "tool_call") {
          // Full trace — args and result included for the opponent.
          messages.push({
            type: "tool_call",
            name: String(event.name ?? "tool"),
            status: String(event.status ?? "unknown"),
            args: event.args,
            result: event.result,
          });
        }
      }

      const result = await run.wait();
      const channel = { messages };
      let rawText = assistantTextFromChannel(channel);
      if (!rawText) {
        rawText = String(result.result ?? "");
        if (rawText) {
          messages.push({ type: "assistant", text: rawText });
        }
      }

      return {
        public: channel,
        rawText,
        usage: normalizeUsage(result.usage ?? run.usage),
        durationMs: Math.max(1, Date.now() - started),
      };
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
      // Mirror tool_use blocks into the public tool_call trace as well.
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

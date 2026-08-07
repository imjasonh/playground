import { mkdir } from "node:fs/promises";
import type {
  AgentFactory,
  PlayerAgent,
  PromptTurn,
  TurnResult,
} from "./types.js";
import type { TokenUsage } from "../types.js";

type SdkModule = typeof import("@cursor/sdk");

let sdkPromise: Promise<SdkModule> | undefined;

function loadSdk(): Promise<SdkModule> {
  sdkPromise ??= import("@cursor/sdk");
  return sdkPromise;
}

/**
 * Cursor SDK-backed player.
 *
 * - Built-in coding tools are disabled (`tools: []` or MCP-only).
 * - Keeper may receive a private `commit_secret` custom tool; its arguments
 *   stay in-process and are never copied into the public channel.
 * - Thinking stream events are captured and published to the opponent.
 */
export const createCursorAgent: AgentFactory = async (options) => {
  const { Agent } = await loadSdk();
  await mkdir(options.workspaceDir, { recursive: true });

  let committedSecret: string | undefined;

  const customTools =
    options.allowCommitSecret
      ? {
          commit_secret: {
            description:
              "Privately commit the secret answer to the game harness. " +
              "Call this exactly once before giving clues. " +
              "The guesser does not see tool arguments — but they DO see your " +
              "thinking and assistant text, so never name the secret there.",
            inputSchema: {
              type: "object",
              properties: {
                secret: {
                  type: "string",
                  description: "The secret the guesser must discover",
                },
              },
              required: ["secret"],
            },
            async execute(args: Record<string, unknown>) {
              const secret = String(args.secret ?? "").trim();
              if (!secret) {
                return {
                  content: [{ type: "text", text: "Error: empty secret" }],
                  isError: true,
                };
              }
              if (committedSecret && committedSecret !== secret) {
                return {
                  content: [
                    {
                      type: "text",
                      text: "Error: secret already committed; cannot change it",
                    },
                  ],
                  isError: true,
                };
              }
              committedSecret = secret;
              options.onCommitSecret?.(secret);
              return `Secret committed (${secret.length} chars). Do not repeat it in thinking or text.`;
            },
          },
        }
      : undefined;

  const agent = await Agent.create({
    apiKey: options.apiKey ?? process.env.CURSOR_API_KEY,
    model: { id: options.model },
    name: `its-not-jaws-${options.role}`,
    // Keeper needs MCP for custom tools; guesser is pure chat.
    tools: options.allowCommitSecret ? ["mcp"] : [],
    local: {
      cwd: options.workspaceDir,
      // Do not inherit project/user MCP, hooks, or skills into the game.
      settingSources: [],
      ...(customTools ? { customTools } : {}),
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
      const thinkingParts: string[] = [];
      const textParts: string[] = [];
      const toolNames: string[] = [];
      const secretBefore = committedSecret;

      const run = await agent.send(input.prompt);

      for await (const event of run.stream()) {
        if (event.type === "thinking") {
          thinkingParts.push(String(event.text ?? ""));
        } else if (event.type === "assistant") {
          textParts.push(extractAssistantText(event));
        } else if (event.type === "tool_call") {
          // Record the name only — never forward args (they may contain the secret).
          toolNames.push(String(event.name ?? "tool"));
        }
      }

      const result = await run.wait();
      const rawText = textParts.join("") || String(result.result ?? "");
      const usage = normalizeUsage(result.usage ?? run.usage);

      const newlyCommitted =
        committedSecret && committedSecret !== secretBefore
          ? committedSecret
          : undefined;

      return {
        public: {
          text: rawText,
          thinking: thinkingParts.join("\n").trim(),
        },
        rawText,
        toolNames: [...new Set(toolNames)],
        committedSecret: newlyCommitted,
        usage,
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
      // SDKAgent.close() is sync; asyncDispose may exist on some versions.
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

function extractAssistantText(event: {
  message?: { content?: Array<{ type?: string; text?: string }> };
}): string {
  const content = event.message?.content;
  if (!Array.isArray(content)) return "";
  return content
    .filter((block) => block?.type === "text" && typeof block.text === "string")
    .map((block) => block.text!)
    .join("");
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

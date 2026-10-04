import type { AgentOptions, AgentUsage, RunResult, SDKMessage } from "@cursor/sdk";
import type { Usage } from "../result.js";
import { toolsFor } from "../tools.js";
import type { AgentResponse, Backend } from "./types.js";

const USAGE_ATTEMPTS = 4;
const USAGE_DELAY_MS = 1500;

/** The parts of the Cursor SDK that the backend uses. */
export interface CursorSdk {
  Agent: { create(options: AgentOptions): Promise<CursorAgent> };
}

export interface CursorAgent {
  send(message: string): Promise<CursorRun>;
  getUsage(): Promise<AgentUsage>;
  [Symbol.asyncDispose](): Promise<void>;
}

export interface CursorRun {
  stream(): AsyncIterable<SDKMessage>;
  wait(): Promise<RunResult>;
  cancel(): Promise<void>;
}

export interface CursorBackendOptions {
  /** Loads the Cursor SDK. */
  load?: () => Promise<CursorSdk>;
  /** How long to wait before reading the agent's usage again. */
  usageDelayMs?: number;
}

/** Returns a backend that runs the agent locally, in this process, with the Cursor SDK. */
export function newCursorBackend(options: CursorBackendOptions = {}): Backend {
  const load: () => Promise<CursorSdk> = options.load ?? (() => import("@cursor/sdk"));
  const usageDelayMs = options.usageDelayMs ?? USAGE_DELAY_MS;
  return async (request) => {
    if (!request.apiKey) {
      throw new Error("the cursor backend needs a Cursor API key");
    }
    const { Agent } = await load();
    const agent = await Agent.create({
      apiKey: request.apiKey,
      model: { id: request.model },
      name: "git-k8s-agent",
      tools: toolsFor(request),
      local: {
        cwd: request.cwd,
        settingSources: [],
        sandboxOptions: { enabled: false },
      },
    });
    try {
      const run = await agent.send(request.prompt);
      let timedOut = false;
      const timer = setTimeout(() => {
        timedOut = true;
        void run.cancel().catch(() => undefined);
      }, request.timeoutMs);
      const texts: string[] = [];
      try {
        for await (const event of run.stream()) {
          if (event.type === "assistant") {
            for (const block of event.message.content) {
              if (block.type === "text") {
                texts.push(block.text);
              }
            }
          } else if (event.type === "tool_call" && event.status !== "running") {
            request.log(`tool ${event.name}: ${event.status}`);
          }
        }
      } finally {
        clearTimeout(timer);
      }
      const result = await run.wait();
      if (timedOut) {
        throw new Error(`the agent didn't finish in ${Math.round(request.timeoutMs / 1000)}s`);
      }
      if (result.status !== "finished") {
        throw new Error(`the agent's run ended with status ${result.status}: ${result.error?.message ?? "no message"}`);
      }
      const billed = await readUsage(() => agent.getUsage(), usageDelayMs);
      const usage = billed?.usage && billed.usage.totalTokens > 0 ? billed.usage : result.usage;
      const response: AgentResponse = {
        text: texts.join("\n") || result.result || "",
        model: request.model,
        usage: tokens(usage),
      };
      const raw = cents(billed?.cost?.rawCostCents);
      const charged = cents(billed?.cost?.chargedCents);
      if (raw !== undefined) {
        response.costCents = raw;
      }
      if (charged !== undefined) {
        response.chargedCents = charged;
      }
      request.log(`the agent finished in ${result.durationMs ?? 0}ms with ${usage?.totalTokens ?? 0} tokens`);
      return response;
    } finally {
      await agent[Symbol.asyncDispose]().catch(() => undefined);
    }
  };
}

/** Runs the agent locally, in this process, with the Cursor SDK. */
export const cursorBackend: Backend = newCursorBackend();

interface Billed {
  usage?: Partial<Usage> & { totalTokens: number };
  cost?: { rawCostCents?: number; chargedCents?: number };
}

/** Reads the agent's billed usage until it includes a cost, which can lag the run. */
async function readUsage(read: () => Promise<Billed>, delayMs: number): Promise<Billed | undefined> {
  let latest: Billed | undefined;
  for (let attempt = 0; attempt < USAGE_ATTEMPTS && !latest?.cost; attempt++) {
    if (attempt > 0) {
      await new Promise((resolve) => {
        setTimeout(resolve, delayMs);
      });
    }
    latest = await read().catch(() => latest);
  }
  return latest;
}

function tokens(usage: Partial<Usage> | undefined): Usage {
  const n = (v: number | undefined) => (typeof v === "number" && Number.isFinite(v) ? Math.max(0, Math.round(v)) : 0);
  return {
    inputTokens: n(usage?.inputTokens),
    outputTokens: n(usage?.outputTokens),
    cacheReadTokens: n(usage?.cacheReadTokens),
    cacheWriteTokens: n(usage?.cacheWriteTokens),
  };
}

function cents(v: number | undefined): number | undefined {
  return typeof v === "number" && Number.isFinite(v) && v >= 0 ? v : undefined;
}

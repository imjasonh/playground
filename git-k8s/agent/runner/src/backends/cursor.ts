import type { Usage } from "../result.js";
import type { AgentResponse, Backend } from "./types.js";

/**
 * The tools that a review may use. The agent gets no shell, MCP servers,
 * subagents, or web access, so it can't run the code it reads or send data
 * anywhere but Cursor's API.
 */
const READ_TOOLS = ["read", "grep", "glob", "ls"];
const EDIT_TOOLS = [...READ_TOOLS, "edit", "delete"];

const USAGE_ATTEMPTS = 4;
const USAGE_DELAY_MS = 1500;

/** Runs the agent locally, in this process, with the Cursor SDK. */
export const cursorBackend: Backend = async (request) => {
  const { Agent } = await import("@cursor/sdk");
  const agent = await Agent.create({
    apiKey: request.apiKey,
    model: { id: request.model },
    name: "git-k8s-agent",
    tools: request.edit ? EDIT_TOOLS : READ_TOOLS,
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
    const billed = await readUsage(() => agent.getUsage());
    const usage = billed?.usage && billed.usage.totalTokens > 0 ? billed.usage : result.usage;
    const response: AgentResponse = {
      text: texts.join("\n") || result.result || "",
      model: request.model,
      usage: tokens(usage),
    };
    if (billed?.cost) {
      response.costCents = billed.cost.rawCostCents;
    }
    request.log(`the agent finished in ${result.durationMs ?? 0}ms with ${usage?.totalTokens ?? 0} tokens`);
    return response;
  } finally {
    await agent[Symbol.asyncDispose]().catch(() => undefined);
  }
};

interface Billed {
  usage?: Partial<Usage> & { totalTokens: number };
  cost?: { rawCostCents: number };
}

/** Reads the agent's billed usage until it includes a cost, which can lag the run. */
async function readUsage(read: () => Promise<Billed>): Promise<Billed | undefined> {
  let latest: Billed | undefined;
  for (let attempt = 0; attempt < USAGE_ATTEMPTS && !latest?.cost; attempt++) {
    if (attempt > 0) {
      await new Promise((resolve) => {
        setTimeout(resolve, USAGE_DELAY_MS);
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

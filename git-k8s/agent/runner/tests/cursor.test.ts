import assert from "node:assert/strict";
import { test } from "node:test";
import type { AgentOptions, AgentUsage, RunResult, SDKMessage } from "@cursor/sdk";
import { type CursorSdk, newCursorBackend } from "../src/backends/cursor.js";
import type { AgentRequest } from "../src/backends/types.js";

interface Script {
  events?: SDKMessage[];
  result?: Partial<RunResult>;
  /** Keeps the stream open until the run is cancelled. */
  hang?: boolean;
  /** What each read of the agent's usage returns; the last one repeats. */
  usage?: AgentUsage[];
}

function fakeSdk(script: Script) {
  const calls = { loads: 0, create: [] as AgentOptions[], sent: [] as string[], cancels: 0, usageReads: 0, disposes: 0 };
  const sdk: CursorSdk = {
    Agent: {
      async create(options) {
        calls.create.push(options);
        return {
          async send(message) {
            calls.sent.push(message);
            let cancelled: () => void = () => undefined;
            const stopped = new Promise<void>((resolve) => {
              cancelled = resolve;
            });
            return {
              async *stream() {
                yield* script.events ?? [];
                if (script.hang) {
                  await stopped;
                }
              },
              async wait() {
                return { id: "run-1", status: "finished", ...script.result };
              },
              async cancel() {
                calls.cancels++;
                cancelled();
              },
            };
          },
          async getUsage() {
            const usage = script.usage ?? [];
            const next = usage[Math.min(calls.usageReads++, usage.length - 1)];
            if (!next) {
              throw new Error("no usage yet");
            }
            return next;
          },
          async [Symbol.asyncDispose]() {
            calls.disposes++;
          },
        };
      },
    },
  };
  const backend = newCursorBackend({
    load: async () => {
      calls.loads++;
      return sdk;
    },
    usageDelayMs: 0,
  });
  return { backend, calls };
}

function request(over: Partial<AgentRequest> = {}): AgentRequest {
  return {
    prompt: "Review the change.",
    diff: "",
    cwd: "/src",
    edit: false,
    model: "composer-2.5",
    apiKey: "key-123",
    timeoutMs: 60_000,
    log: () => undefined,
    ...over,
  };
}

const text = (t: string): SDKMessage => ({
  type: "assistant",
  agent_id: "a",
  run_id: "r",
  message: { role: "assistant", content: [{ type: "text", text: t }] },
});

const tokens = (n: number) => ({ inputTokens: n, outputTokens: n, cacheReadTokens: 0, cacheWriteTokens: 0, totalTokens: 2 * n });

test("creates the agent with only the tools that the task allows", async () => {
  const { backend, calls } = fakeSdk({ events: [text("ok")] });
  await backend(request());
  await backend(request({ edit: true, cwd: "/work" }));
  const want = (tools: string[], cwd: string): AgentOptions => ({
    apiKey: "key-123",
    model: { id: "composer-2.5" },
    name: "git-k8s-agent",
    tools: tools as AgentOptions["tools"],
    local: { cwd, settingSources: [], sandboxOptions: { enabled: false } },
  });
  assert.deepEqual(calls.create, [want(["read", "grep", "glob", "ls"], "/src"), want(["read", "grep", "glob", "ls", "edit", "delete"], "/work")]);
  assert.deepEqual(calls.sent, ["Review the change.", "Review the change."]);
  assert.equal(calls.disposes, 2);
});

test("returns the agent's text, its usage, and both costs", async () => {
  const logs: string[] = [];
  const toolCall: SDKMessage = { type: "tool_call", agent_id: "a", run_id: "r", call_id: "c", name: "read", status: "completed" };
  const { backend } = fakeSdk({
    events: [text("I read it."), toolCall, text('{"verdict": "pass"}')],
    result: { usage: tokens(1) },
    usage: [
      {
        usage: { inputTokens: 10.4, outputTokens: -3, cacheReadTokens: Number.NaN, cacheWriteTokens: 7, totalTokens: 17 },
        cost: { rawCostCents: 1.25, chargedCents: 0 },
        runs: [],
      },
    ],
  });
  const response = await backend(request({ log: (line) => logs.push(line) }));
  assert.deepEqual(response, {
    text: 'I read it.\n{"verdict": "pass"}',
    model: "composer-2.5",
    usage: { inputTokens: 10, outputTokens: 0, cacheReadTokens: 0, cacheWriteTokens: 7 },
    costCents: 1.25,
    chargedCents: 0,
  });
  assert.ok(logs.includes("tool read: completed"));
});

test("waits for the cost, then falls back to the run's usage", async () => {
  const late = fakeSdk({
    usage: [
      { usage: tokens(5), runs: [] },
      { usage: tokens(5), cost: { rawCostCents: 2, chargedCents: 3 }, runs: [] },
    ],
  });
  const response = await late.backend(request());
  assert.equal(late.calls.usageReads, 2);
  assert.deepEqual([response.costCents, response.chargedCents], [2, 3]);

  const never = fakeSdk({ result: { usage: tokens(4), result: "the answer" }, usage: [{ usage: tokens(0), runs: [] }] });
  const fallback = await never.backend(request());
  assert.equal(never.calls.usageReads, 4);
  assert.equal(fallback.text, "the answer");
  assert.deepEqual(fallback.usage, { inputTokens: 4, outputTokens: 4, cacheReadTokens: 0, cacheWriteTokens: 0 });
  assert.equal(fallback.costCents, undefined);
  assert.equal(fallback.chargedCents, undefined);

  const broken = fakeSdk({ usage: [{ usage: tokens(1), cost: { rawCostCents: -1, chargedCents: Number.POSITIVE_INFINITY }, runs: [] }] });
  const odd = await broken.backend(request());
  assert.deepEqual([odd.costCents, odd.chargedCents], [undefined, undefined]);
});

test("cancels a run that takes too long", async () => {
  const { backend, calls } = fakeSdk({ hang: true, result: { status: "cancelled" } });
  await assert.rejects(backend(request({ timeoutMs: 20 })), /the agent didn't finish in 0s/);
  assert.equal(calls.cancels, 1);
  assert.equal(calls.disposes, 1);
});

test("fails a run that doesn't finish", async () => {
  for (const [result, want] of [
    [{ status: "error", error: { message: "rate limited" } }, /ended with status error: rate limited/],
    [{ status: "cancelled" }, /ended with status cancelled: no message/],
  ] as const) {
    const { backend, calls } = fakeSdk({ events: [text('{"verdict": "pass"}')], result });
    await assert.rejects(backend(request()), want);
    assert.equal(calls.disposes, 1);
    assert.equal(calls.usageReads, 0);
  }
});

test("needs an API key before it loads the SDK", async () => {
  const { backend, calls } = fakeSdk({});
  await assert.rejects(backend(request({ apiKey: "" })), /needs a Cursor API key/);
  assert.equal(calls.loads, 0);
});

import assert from "node:assert/strict";
import { test } from "node:test";
import { runLoop, type LoopDeps } from "../src/loop.js";
import type { Advisor, Capture, Controls, SidebarView } from "../src/types.js";

type Tick = { t: number; screen?: string; dead?: boolean; ask?: boolean; toggle?: boolean };

function harness(script: Tick[]) {
  const clock = { t: 0 };
  const prompts: string[] = [];
  const views: SidebarView[] = [];
  let captureIdx = 0;
  let controlIdx = 0;
  let adviceN = 0;

  const advisor: Advisor = {
    async advise(prompt: string) {
      prompts.push(prompt);
      adviceN++;
      return { text: `tip ${adviceN}`, usage: { inputTokens: 10, outputTokens: 5, totalTokens: 15 } };
    },
    async getBilledUsage() {
      return { usage: { inputTokens: 0, outputTokens: 0, totalTokens: 0 }, rawCostCents: 7 };
    },
    async dispose() {},
  };

  const deps: LoopDeps = {
    async capture(): Promise<Capture> {
      const tick = script[captureIdx++];
      if (!tick || tick.screen === undefined) return { ok: false };
      clock.t = tick.t;
      return { ok: true, screen: tick.screen, dead: tick.dead ?? false };
    },
    async controls(): Promise<Controls> {
      const tick = script[controlIdx++];
      return { ask: tick?.ask ?? false, toggle: tick?.toggle ?? false };
    },
    advisor,
    paint: (view) => views.push(view),
    now: () => clock.t,
    sleep: async () => {},
  };

  return { deps, prompts, views };
}

const OPTS = { settleMs: 700, cooldownMs: 6_000, pollMs: 400, maxTicks: 50 };

test("advises once the screen settles, then stays quiet while unchanged", async () => {
  const { deps, prompts } = harness([
    { t: 0, screen: "@ board" },
    { t: 1_000, screen: "@ board" },
    { t: 2_000, screen: "@ board" },
  ]);
  const summary = await runLoop(deps, OPTS);
  assert.equal(summary.adviceCount, 1);
  assert.equal(prompts.length, 1);
  assert.match(prompts[0], /@ board/);
  assert.equal(summary.usage.totalTokens, 15);
});

test("the ask hotkey forces advice despite cooldown and an unchanged screen", async () => {
  const { deps } = harness([
    { t: 0, screen: "room" },
    { t: 1_000, screen: "room" },
    { t: 1_500, screen: "room", ask: true },
  ]);
  const summary = await runLoop(deps, OPTS);
  assert.equal(summary.adviceCount, 2);
});

test("toggling auto off stops automatic advice", async () => {
  const { deps, views } = harness([
    { t: 0, screen: "room", toggle: true },
    { t: 2_000, screen: "hall" },
  ]);
  const summary = await runLoop(deps, OPTS);
  assert.equal(summary.adviceCount, 0);
  assert.ok(views.some((v) => v.auto === false && v.status === "paused"));
});

test("a dead pane ends advice, shows a final panel, and reads the billed cost", async () => {
  const { deps, views } = harness([
    { t: 0, screen: "You die.", dead: true },
    { t: 10, screen: "You die.", dead: true },
  ]);
  const summary = await runLoop(deps, OPTS);
  assert.equal(summary.adviceCount, 0);
  assert.equal(summary.costCents, 7);
  assert.ok(views.some((v) => v.status === "over"));
});

test("a missing pane ends the loop right away", async () => {
  const { deps } = harness([]);
  const summary = await runLoop(deps, OPTS);
  assert.equal(summary.adviceCount, 0);
  assert.equal(summary.ticks, 1);
});

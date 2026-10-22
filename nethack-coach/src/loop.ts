import { decideAdvice } from "./advice.js";
import { addUsage, emptyUsage } from "./cost.js";
import { diffScreens, screensEqual } from "./screen.js";
import { turnPrompt } from "./prompts.js";
import type { Advisor, Capture, Controls, SidebarView, TokenUsage } from "./types.js";

export type LoopDeps = {
  capture: () => Promise<Capture>;
  controls: () => Promise<Controls>;
  advisor: Advisor;
  paint: (view: SidebarView) => void;
  now: () => number;
  sleep: (ms: number) => Promise<void>;
};

export type LoopOptions = {
  settleMs: number;
  cooldownMs: number;
  pollMs: number;
  /** Test-only cap so a fake loop can never spin forever. */
  maxTicks?: number;
};

export type LoopSummary = {
  ticks: number;
  adviceCount: number;
  usage: TokenUsage;
  costCents?: number;
};

/**
 * Watch the game pane and advise. Runs until the pane disappears (the session was
 * killed), then reports what it spent. A dead-but-present pane ends advice and
 * leaves a final panel up so the player can read it.
 */
export async function runLoop(deps: LoopDeps, options: LoopOptions): Promise<LoopSummary> {
  let auto = true;
  let lastScreen: string | undefined;
  let lastChangeAt = deps.now();
  let changedSinceAdvice = false;
  let lastAdvisedScreen: string | undefined;
  let lastAdvice = "";
  let lastAdviceAt = Number.NEGATIVE_INFINITY;
  let over = false;

  let usage = emptyUsage();
  let costCents: number | undefined;
  let adviceCount = 0;
  let ticks = 0;
  let lastPainted = "";

  const show = (view: SidebarView): void => {
    const signature = JSON.stringify(view);
    if (signature === lastPainted) return;
    lastPainted = signature;
    deps.paint(view);
  };

  const viewNow = (status: SidebarView["status"]): SidebarView => ({
    status,
    auto,
    advice: lastAdvice,
    tokens: usage.totalTokens,
    costCents,
  });

  for (;;) {
    if (options.maxTicks !== undefined && ticks >= options.maxTicks) break;
    ticks++;

    const capture = await deps.capture();
    if (!capture.ok) break;

    const controls = await deps.controls();
    if (controls.toggle) auto = !auto;

    const now = deps.now();
    const screen = capture.screen;
    if (lastScreen === undefined || !screensEqual(screen, lastScreen)) {
      lastScreen = screen;
      lastChangeAt = now;
      changedSinceAdvice = true;
    }

    if (capture.dead) {
      if (!over) {
        over = true;
        show(viewNow("over"));
        costCents = await billedCost(deps.advisor, costCents);
        show(viewNow("over"));
      }
      await deps.sleep(options.pollMs);
      continue;
    }

    const decision = decideAdvice({
      forcedAsk: controls.ask,
      auto,
      dead: false,
      changedSinceAdvice,
      screenEqualsLastAdvised:
        lastAdvisedScreen !== undefined && screensEqual(screen, lastAdvisedScreen),
      now,
      lastChangeAt,
      lastAdviceAt,
      settleMs: options.settleMs,
      cooldownMs: options.cooldownMs,
    });

    if (!decision.advise) {
      show(viewNow(auto ? "watching" : "paused"));
      await deps.sleep(options.pollMs);
      continue;
    }

    show(viewNow("thinking"));
    const diff = lastAdvisedScreen ? diffScreens(lastAdvisedScreen, screen) : undefined;
    const advice = await deps.advisor.advise(
      turnPrompt({ screen, diff: diff || undefined, lastAdvice: lastAdvice || undefined, forced: controls.ask }),
    );
    usage = addUsage(usage, advice.usage);
    adviceCount++;
    lastAdvice = advice.text || lastAdvice;
    lastAdvisedScreen = screen;
    lastAdviceAt = deps.now();
    changedSinceAdvice = false;
    show(viewNow(auto ? "watching" : "paused"));

    await deps.sleep(options.pollMs);
  }

  costCents = await billedCost(deps.advisor, costCents);
  return { ticks, adviceCount, usage, costCents };
}

async function billedCost(advisor: Advisor, current: number | undefined): Promise<number | undefined> {
  if (!advisor.getBilledUsage) return current;
  try {
    const billed = await advisor.getBilledUsage();
    return billed.rawCostCents ?? current;
  } catch {
    return current;
  }
}

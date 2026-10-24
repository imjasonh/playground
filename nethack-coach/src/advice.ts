/** Inputs for one advice decision. All times are millisecond clock readings. */
export type AdviceState = {
  /** The player pressed the ask hotkey since the last decision. */
  forcedAsk: boolean;
  /** Automatic advice is on. */
  auto: boolean;
  /** The game pane is a dead pane (the game exited). */
  dead: boolean;
  /** The screen changed since the last advice was given. */
  changedSinceAdvice: boolean;
  /** The current screen equals the one the last advice spoke to. */
  screenEqualsLastAdvised: boolean;
  now: number;
  /** When the screen last changed. */
  lastChangeAt: number;
  /** When advice was last given, or -Infinity if never. */
  lastAdviceAt: number;
  /** How long the screen must hold still before auto advice fires. */
  settleMs: number;
  /** Minimum gap between two auto-advice calls. */
  cooldownMs: number;
};

export type AdviceDecision = {
  advise: boolean;
  reason:
    | "forced"
    | "settled"
    | "game-over"
    | "auto-off"
    | "unchanged"
    | "not-settled"
    | "cooldown";
};

/**
 * Decide whether to ask the model for advice this tick.
 *
 * An explicit ask always wins, even over the cooldown, so the player can request
 * help at any moment. Automatic advice waits for the screen to settle and
 * respects a cooldown, so a flurry of redraws becomes one call rather than many.
 */
export function decideAdvice(state: AdviceState): AdviceDecision {
  if (state.forcedAsk) return { advise: true, reason: "forced" };
  if (state.dead) return { advise: false, reason: "game-over" };
  if (!state.auto) return { advise: false, reason: "auto-off" };
  if (!state.changedSinceAdvice || state.screenEqualsLastAdvised) {
    return { advise: false, reason: "unchanged" };
  }
  if (state.now - state.lastChangeAt < state.settleMs) {
    return { advise: false, reason: "not-settled" };
  }
  if (state.now - state.lastAdviceAt < state.cooldownMs) {
    return { advise: false, reason: "cooldown" };
  }
  return { advise: true, reason: "settled" };
}

/** Budgets for one run. These bound cost. They do not encode game progress. */
export const LIMITS = {
  DEFAULT_MAX_TURNS: 24,
  MAX_MAX_TURNS: 200,
  DEFAULT_LIVES: 2,
  MAX_LIVES: 50,
  MAX_KEYS_PER_TURN: 32,
  MAX_PROCEDURE_KEYS: 64,
  MAX_NOTE_CHARS: 500,
  MAX_NOTES_IN_PROMPT: 40,
  MAX_ENDINGS_IN_PROMPT: 5,
  MAX_PROMPT_MEMORY_CHARS: 12_000,
  TURN_TIMEOUT_MS: 5 * 60 * 1000,
  DEFAULT_MODEL: "composer-2.5",
  DEFAULT_TTY_IDLE_MS: 150,
  DEFAULT_TTY_START_MS: 8_000,
} as const;

export function clampMaxTurns(value: number): number {
  if (!Number.isFinite(value) || value < 1) return LIMITS.DEFAULT_MAX_TURNS;
  return Math.min(Math.floor(value), LIMITS.MAX_MAX_TURNS);
}

export function clampLives(value: number): number {
  if (!Number.isFinite(value) || value < 1) return LIMITS.DEFAULT_LIVES;
  return Math.min(Math.floor(value), LIMITS.MAX_LIVES);
}

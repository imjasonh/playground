/** Budgets for one run. These bound cost. They do not encode game progress. */
export const LIMITS = {
  DEFAULT_MAX_TURNS: 24,
  MAX_MAX_TURNS: 200,
  DEFAULT_LIVES: 2,
  MAX_LIVES: 50,
  MAX_KEYS_PER_TURN: 32,
  /** A reusable sequence, not a walk across one screen. */
  MAX_PROCEDURE_KEYS: 12,
  MAX_PROCEDURES: 12,
  MAX_NOTE_CHARS: 280,
  /** Claims that survive the screen. A turn log does not belong here. */
  MAX_LIVE_NOTES: 24,
  MAX_NOTES_PER_LIFE: 3,
  MAX_NOTES_IN_PROMPT: 24,
  MAX_ENDINGS_STORED: 6,
  MAX_ENDINGS_IN_PROMPT: 6,
  MAX_ENDING_CHARS: 480,
  MAX_PROMPT_MEMORY_CHARS: 12_000,
  TURN_TIMEOUT_MS: 5 * 60 * 1000,
  DEFAULT_MODEL: "grok-4.6",
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

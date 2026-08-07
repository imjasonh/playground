/** Hard caps to keep live Cursor games from runaway token spend. */

export const LIMITS = {
  DEFAULT_MAX_TURNS: 8,
  MIN_MAX_TURNS: 1,
  /** Guesser turns per game (each turn can be two agent calls). */
  MAX_MAX_TURNS: 24,

  DEFAULT_GAMES_PER_MATCHUP: 2,
  MAX_GAMES_PER_MATCHUP: 10,

  /** |models|² matchups; keep under GitHub's 256-job matrix cap. */
  MAX_MODELS: 12,
  MAX_MATRIX_JOBS: 256,

  /** Cancel a hung Cursor agent turn after this many ms. */
  TURN_TIMEOUT_MS: 5 * 60 * 1000,

  /**
   * When forwarding a turn to the opponent, truncate the rendered trace.
   * Agents already retain their own history; this bounds prompt growth.
   */
  MAX_TRACE_CHARS_FOR_OPPONENT: 12_000,

  MAX_REPORTED_LEAKED_CLUES: 20,
  MAX_LEAKED_CLUE_TEXT_CHARS: 500,
} as const;

export function clampInt(
  value: number,
  min: number,
  max: number,
  fallback: number,
): number {
  if (!Number.isFinite(value)) return fallback;
  return Math.min(max, Math.max(min, Math.trunc(value)));
}

export function clampMaxTurns(value: number): number {
  return clampInt(
    value,
    LIMITS.MIN_MAX_TURNS,
    LIMITS.MAX_MAX_TURNS,
    LIMITS.DEFAULT_MAX_TURNS,
  );
}

export function clampGamesPerMatchup(value: number): number {
  return clampInt(
    value,
    1,
    LIMITS.MAX_GAMES_PER_MATCHUP,
    LIMITS.DEFAULT_GAMES_PER_MATCHUP,
  );
}

export function assertModelListSize(models: string[]): void {
  if (models.length === 0) {
    throw new Error("No models specified");
  }
  if (models.length > LIMITS.MAX_MODELS) {
    throw new Error(
      `Too many models (${models.length}); max is ${LIMITS.MAX_MODELS}`,
    );
  }
}

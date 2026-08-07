/**
 * Pluggable game rules. See GAME.md for the canonical It's Not Jaws rules.
 *
 * The knower picks the secret. The harness only validates / scores —
 * it does not choose from a title list.
 */
export type GameDefinition = {
  id: string;
  title: string;
  /** Instructions injected into the knower system prompt. */
  knowerBrief: string;
  /** Instructions injected into the guesser system prompt. */
  guesserBrief: string;
  /**
   * True when the secret looks like a fair, well-known-enough movie title.
   * Used when the guesser gives up / hits max turns:
   *   fair → knower_wins; unfair → unguessable.
   * Heuristic only for now — not an allowlist the harness samples from.
   */
  isFairSecret(secret: string): boolean;
  /** Optional domain hint for prompts. */
  domainHint?: string;
};

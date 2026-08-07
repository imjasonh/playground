/**
 * Pluggable game rules. The stub is a stand-in until the real
 * "It's Not Jaws" rules are specified.
 *
 * The knower picks the secret. The harness only validates / scores —
 * it does not choose from a word list.
 */
export type GameDefinition = {
  id: string;
  title: string;
  /** Instructions injected into the knower system prompt. */
  knowerBrief: string;
  /** Instructions injected into the guesser system prompt. */
  guesserBrief: string;
  /**
   * Return false when the secret could not fairly be guessed from clues
   * (blocked domain, private trivia, empty, etc.). Heuristic only — not an
   * allowlist the harness samples from.
   */
  isGuessable(secret: string): boolean;
  /** Optional domain hint for prompts. */
  domainHint?: string;
};

/**
 * Pluggable game rules. The stub is a stand-in until the real
 * "It's Not Jaws" rules are specified.
 */
export type GameDefinition = {
  id: string;
  title: string;
  /** Instructions injected into the keeper system prompt (secret is added separately). */
  keeperBrief: string;
  /** Instructions injected into the guesser system prompt. */
  guesserBrief: string;
  /**
   * Return false when the secret could not fairly be guessed from clues
   * (out of domain, private to the keeper, empty, etc.).
   */
  isGuessable(secret: string): boolean;
  /**
   * Harness picks the secret and injects it into the keeper's private setup.
   * Guesser never sees this assignment — only messages the keeper emits.
   */
  pickSecret(seed?: number): string;
  /** Optional allowlist / domain hint for prompts. */
  domainHint?: string;
};

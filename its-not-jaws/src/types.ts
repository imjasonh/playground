/** Terminal outcomes for a finished game. Extensible as we discover new failure modes. */
export type OutcomeKind =
  | "guesser_correct"
  | "guesser_gave_up"
  | "secret_leaked"
  | "unguessable"
  | "max_turns"
  | "protocol_error"
  | "aborted";

export type PlayerRole = "keeper" | "guesser";

export type TokenUsage = {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens?: number;
  cacheWriteTokens?: number;
  reasoningTokens?: number;
  totalTokens: number;
};

export type CostCents = {
  /** Undiscounted model token cost in cents, when the SDK reports it. */
  rawCostCents: number;
};

export type PlayerUsage = {
  role: PlayerRole;
  model?: string;
  tokens: TokenUsage;
  cost?: CostCents;
  turns: number;
};

export type PublicChannel = {
  /** Assistant-visible text (clues, guesses, dialogue). */
  text: string;
  /** Published thinking / reasoning the opponent is allowed to see. */
  thinking: string;
};

export type AgentTurn = {
  role: PlayerRole;
  turnIndex: number;
  /** Wall-clock ms for this turn. */
  durationMs: number;
  public: PublicChannel;
  /** Tool names invoked this turn (args are never forwarded to the opponent). */
  toolNames: string[];
  usage?: TokenUsage;
  /** Structured move parsed from the assistant text, if any. */
  move?: Move;
  /** Raw assistant text before move extraction. */
  rawText: string;
};

/** Structured moves exchanged on the public channel. */
export type Move =
  | { type: "clue"; text: string }
  | { type: "guess"; value: string }
  | { type: "give_up"; reason?: string }
  | { type: "meta"; text: string };

export type Outcome = {
  kind: OutcomeKind;
  reason: string;
  /** Winning guess, leaked excerpt, etc. */
  detail?: string;
};

export type GameRecord = {
  id: string;
  game: string;
  startedAt: string;
  finishedAt: string;
  keeperModel?: string;
  guesserModel?: string;
  backend: "mock" | "cursor";
  /** Ground-truth secret committed via the private harness tool (or mock). */
  secret?: string;
  secretCommitted: boolean;
  turns: AgentTurn[];
  outcome: Outcome;
  usage: {
    keeper: PlayerUsage;
    guesser: PlayerUsage;
    totalTokens: number;
    totalRawCostCents?: number;
  };
  /** Number of public clue/guess exchanges (excludes setup). */
  gameLength: number;
};

export type HarnessConfig = {
  gameId: string;
  maxTurns: number;
  backend: "mock" | "cursor";
  keeperModel: string;
  guesserModel: string;
  apiKey?: string;
  /** Directory for per-player empty workspaces (Cursor local cwd). */
  workspacesRoot: string;
  /** Where to write the JSON game record. */
  resultsDir: string;
  /** Optional seed for deterministic mock play. */
  seed?: number;
  verbose?: boolean;
};

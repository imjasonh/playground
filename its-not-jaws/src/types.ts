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

/**
 * Everything the agent emitted that the opponent is allowed (and required) to see.
 * Includes thinking, assistant text, and full tool-call traces (name, args, result).
 */
export type TraceMessage =
  | { type: "thinking"; text: string }
  | { type: "assistant"; text: string }
  | {
      type: "tool_call";
      name: string;
      status: string;
      args?: unknown;
      result?: unknown;
    };

export type PublicChannel = {
  /** Ordered stream of agent-emitted messages for this turn. */
  messages: TraceMessage[];
};

export type AgentTurn = {
  role: PlayerRole;
  turnIndex: number;
  /** Wall-clock ms for this turn. */
  durationMs: number;
  public: PublicChannel;
  usage?: TokenUsage;
  /** Structured move parsed from assistant text, if any. */
  move?: Move;
  /** Concatenated assistant text (for move parsing). */
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
  /**
   * Ground-truth secret assigned by the harness and injected into the keeper's
   * private setup prompt (not a message from the keeper, so not shown to the guesser).
   */
  secret: string;
  turns: AgentTurn[];
  outcome: Outcome;
  usage: {
    keeper: PlayerUsage;
    guesser: PlayerUsage;
    totalTokens: number;
    totalRawCostCents?: number;
  };
  /** Number of guesser turns. */
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
  /** Optional seed for deterministic secret pick / mock play. */
  seed?: number;
  /** Override harness-assigned secret (tests). */
  secret?: string;
  verbose?: boolean;
};

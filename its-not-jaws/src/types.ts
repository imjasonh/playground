/** Terminal outcomes for a finished game. Extensible as we discover new failure modes. */
export type OutcomeKind =
  | "guesser_correct"
  | "knower_wins"
  | "secret_leaked"
  | "unguessable"
  | "max_turns"
  | "protocol_error"
  | "aborted";

export type PlayerRole = "knower" | "guesser";

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
 * Everything the agent emitted on a turn.
 * During gameplay, the opponent sees the full trace (thinking, text, tool calls).
 * Setup turns are harness-private and are not forwarded.
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
  /**
   * `setup` = knower commits the secret to the harness only (not shown to guesser).
   * `play` = gameplay; full trace is forwarded to the opponent.
   * `debrief` = post-win guesser report of leaked-clue use (not shown to knower).
   */
  phase: "setup" | "play" | "debrief";
  durationMs: number;
  public: PublicChannel;
  usage?: TokenUsage;
  /** Structured move parsed from assistant text, if any. */
  move?: Move;
  /** Concatenated assistant text (for move parsing). */
  rawText: string;
};

/** Structured moves. `commit` is setup-only and never forwarded to the guesser. */
export type Move =
  | { type: "commit"; secret: string }
  /** Fact shared by the guesser's last guess and the knower's movie. */
  | { type: "shared_fact"; text: string }
  | {
      type: "guess";
      value: string;
      /**
       * Whether this guess relied on non-title clues leaked in the knower's
       * published traces (usually thinking). Required on every guess.
       */
      usedLeakedClues?: boolean;
      /** Clues the guesser reports using. Empty when usedLeakedClues is false. */
      leakedClues?: ReportedLeakedClue[];
    }
  | {
      type: "leak_report";
      usedLeakedClues: boolean;
      leakedClues: ReportedLeakedClue[];
    }
  | { type: "give_up"; reason?: string }
  | { type: "meta"; text: string };

export type Outcome = {
  kind: OutcomeKind;
  reason: string;
  /** Winning guess, leaked excerpt, etc. */
  detail?: string;
};

/** One clue the guesser says they used from the knower's published traces. */
export type ReportedLeakedClue = {
  text: string;
  channel?: "thinking" | "assistant" | "tool_call";
};

/**
 * Guesser-authored report of whether non-title leaked clues helped them win.
 * The harness does not scrape traces to invent this — it only records what B emits.
 */
export type GuesserLeakReport = {
  usedLeakedClues: boolean;
  leakedClues: ReportedLeakedClue[];
  /** Where the structured report came from. */
  source: "winning_guess" | "debrief";
  /** False when the winning guess omitted the report fields and debrief also failed. */
  reported: boolean;
};

export type GameRecord = {
  id: string;
  game: string;
  startedAt: string;
  finishedAt: string;
  knowerModel?: string;
  guesserModel?: string;
  backend: "mock" | "cursor";
  /**
   * Ground-truth secret chosen by the knower during the private setup turn.
   * Parsed from a structured commit move — the harness does not pick it.
   */
  secret?: string;
  secretCommitted: boolean;
  turns: AgentTurn[];
  outcome: Outcome;
  /**
   * Guesser-reported use of non-title leaked clues on the winning guess
   * (or a short debrief if the winning guess omitted the fields).
   */
  guesserLeakReport?: GuesserLeakReport;
  usage: {
    knower: PlayerUsage;
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
  knowerModel: string;
  guesserModel: string;
  apiKey?: string;
  /** Directory for per-player empty workspaces (Cursor local cwd). */
  workspacesRoot: string;
  /** Where to write the JSON game record. */
  resultsDir: string;
  /** Optional seed reserved for future deterministic mock helpers. */
  seed?: number;
  verbose?: boolean;
};

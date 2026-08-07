import type { PublicChannel, TokenUsage } from "../types.js";

export type PromptTurn = {
  /** User-role message delivered to this agent for the turn. */
  prompt: string;
};

export type TurnResult = {
  public: PublicChannel;
  rawText: string;
  toolNames: string[];
  usage?: TokenUsage;
  durationMs: number;
  /**
   * Secret committed via the private `commit_secret` harness tool this turn.
   * Never forwarded to the opponent.
   */
  committedSecret?: string;
};

export type PlayerAgent = {
  readonly role: "keeper" | "guesser";
  readonly model?: string;
  /** Send one prompt and collect the public channel + private side effects. */
  turn(input: PromptTurn): Promise<TurnResult>;
  /** Billed usage snapshot when the backend supports it. */
  getBilledUsage?(): Promise<{
    totalTokens: number;
    rawCostCents: number;
  }>;
  dispose(): Promise<void>;
};

export type AgentFactoryOptions = {
  role: "keeper" | "guesser";
  model: string;
  systemPrompt: string;
  workspaceDir: string;
  apiKey?: string;
  /**
   * When true (keeper only), expose the private `commit_secret` tool.
   * Tool args are harness-private and never copied into the public channel.
   */
  allowCommitSecret?: boolean;
  onCommitSecret?: (secret: string) => void;
  /** Mock-only knobs. */
  seed?: number;
  script?: MockScript;
};

/** Deterministic mock behavior for unit tests. */
export type MockScript = {
  /** Responses in order; after exhaustion, repeats the last or errors. */
  turns: Array<{
    text: string;
    thinking?: string;
    commitSecret?: string;
  }>;
};

export type AgentFactory = (options: AgentFactoryOptions) => Promise<PlayerAgent>;

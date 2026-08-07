import type { PlayerRole, PublicChannel, TokenUsage } from "../types.js";

export type PromptTurn = {
  /** User-role message delivered to this agent for the turn. */
  prompt: string;
};

export type TurnResult = {
  /** Full emitted trace for this turn. */
  public: PublicChannel;
  rawText: string;
  usage?: TokenUsage;
  durationMs: number;
};

export type PlayerAgent = {
  readonly role: PlayerRole;
  readonly model?: string;
  /** Send one prompt and collect the full emitted channel. */
  turn(input: PromptTurn): Promise<TurnResult>;
  /** Billed usage snapshot when the backend supports it. */
  getBilledUsage?(): Promise<{
    totalTokens: number;
    rawCostCents: number;
  }>;
  dispose(): Promise<void>;
};

export type AgentFactoryOptions = {
  role: PlayerRole;
  model: string;
  systemPrompt: string;
  workspaceDir: string;
  apiKey?: string;
  /** Cancel a hung Cursor turn after this many ms (cursor backend). */
  turnTimeoutMs?: number;
  /** Mock-only knobs. */
  seed?: number;
  script?: MockScript;
};

/** Deterministic mock behavior for unit tests. */
export type MockScript = {
  /** Responses in order; after exhaustion, uses a role-specific fallback. */
  turns: Array<{
    text: string;
    thinking?: string;
    toolCalls?: Array<{
      name: string;
      status?: string;
      args?: unknown;
      result?: unknown;
    }>;
  }>;
};

export type AgentFactory = (options: AgentFactoryOptions) => Promise<PlayerAgent>;

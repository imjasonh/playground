import type { PublicChannel, TokenUsage } from "../types.js";

export type PromptTurn = {
  /** User-role message delivered to this agent for the turn. */
  prompt: string;
};

export type TurnResult = {
  /** Full published trace for the opponent (thinking, text, tool calls). */
  public: PublicChannel;
  rawText: string;
  usage?: TokenUsage;
  durationMs: number;
};

export type PlayerAgent = {
  readonly role: "keeper" | "guesser";
  readonly model?: string;
  /** Send one prompt and collect the full public channel. */
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
  /** Mock-only knobs. */
  seed?: number;
  script?: MockScript;
};

/** Deterministic mock behavior for unit tests. */
export type MockScript = {
  /** Responses in order; after exhaustion, errors. */
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

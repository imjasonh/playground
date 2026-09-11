import type { TokenUsage, TraceMessage } from "../types.js";

export type PromptTurn = {
  prompt: string;
};

export type TurnResult = {
  rawText: string;
  messages: TraceMessage[];
  usage?: TokenUsage;
  durationMs: number;
};

export type PlayerAgent = {
  readonly model?: string;
  turn(input: PromptTurn): Promise<TurnResult>;
  getBilledUsage?(): Promise<{
    totalTokens: number;
    rawCostCents: number;
  }>;
  dispose(): Promise<void>;
};

export type MockTurn = {
  text: string;
  thinking?: string;
};

export type MockScript = {
  turns: MockTurn[];
  /** Filled by the mock with each prompt it received. */
  seenPrompts?: string[];
};

export type AgentFactoryOptions = {
  model: string;
  systemPrompt: string;
  workspaceDir: string;
  apiKey?: string;
  turnTimeoutMs?: number;
  script?: MockScript;
};

export type AgentFactory = (options: AgentFactoryOptions) => Promise<PlayerAgent>;

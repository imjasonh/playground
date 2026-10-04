import type { Usage } from "../result.js";

/** What a backend needs to run one agent task. */
export interface AgentRequest {
  prompt: string;
  /** The whole lines of the change from the merge base to the head that the prompt holds. */
  diff: string;
  /** The work tree, which the agent works in. */
  cwd: string;
  edit: boolean;
  model: string;
  apiKey: string;
  timeoutMs: number;
  log: (line: string) => void;
}

/** What the agent answered, and what the answer cost. */
export interface AgentResponse {
  text: string;
  model: string;
  usage: Usage;
  /** The run's model token cost before discounts, the SDK's rawCostCents. */
  costCents?: number;
  /** What Cursor charged for the run, the SDK's chargedCents. */
  chargedCents?: number;
}

/**
 * Runs an agent. The operator chooses a backend for each task, so where
 * the agent runs is hidden from it.
 */
export type Backend = (request: AgentRequest) => Promise<AgentResponse>;

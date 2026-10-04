import type { Usage } from "../result.js";

/** What a backend needs to run one agent task. */
export interface AgentRequest {
  prompt: string;
  /** The whole lines of the change from the merge base to the head that the prompt holds. */
  diff: string;
  /** The work tree, which the agent works in. */
  cwd: string;
  edit: boolean;
  /** The agent's tools, if not all that edit allows. */
  tools?: string[];
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

/** What an agent's run used, and what it cost. */
export type Spent = Omit<AgentResponse, "text">;

/**
 * Says why an agent's run failed after it started, with what the run used,
 * so the runner can report the cost of a run that failed.
 */
export class AgentError extends Error {
  readonly spent: Spent;

  constructor(message: string, spent: Spent) {
    super(message);
    this.name = "AgentError";
    this.spent = spent;
  }
}

/**
 * Runs an agent. The operator chooses a backend for each task, so where
 * the agent runs is hidden from it. A backend throws an AgentError when the
 * run fails after it started and the backend knows what the run used.
 */
export type Backend = (request: AgentRequest) => Promise<AgentResponse>;

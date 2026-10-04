import type { Usage } from "../result.js";

/** What a backend needs to run one agent task. */
export interface AgentRequest {
  prompt: string;
  /** The change from the merge base to the head, which the prompt also holds. */
  diff: string;
  /** The work tree, which the agent works in. */
  cwd: string;
  edit: boolean;
  /** For a task that merges, the files that conflict, which hold conflict markers. */
  conflicts?: string[];
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
  costCents?: number;
}

/**
 * Runs an agent. The operator chooses a backend for each task, so where
 * the agent runs is hidden from it.
 */
export type Backend = (request: AgentRequest) => Promise<AgentResponse>;

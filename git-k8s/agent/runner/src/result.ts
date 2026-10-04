/** Token counts that the SDK reported for a run. */
export interface Usage {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens: number;
  cacheWriteTokens: number;
}

/**
 * A file that the agent changed. Content is base64. A deleted file has only
 * its path and deleted.
 */
export interface ChangedFile {
  path: string;
  mode?: "100644" | "100755" | "120000";
  content?: string;
  deleted?: boolean;
}

/** What the runner reports to the operator, as JSON. */
export interface Result {
  verdict: "pass" | "fail";
  summary: string;
  reasoning: string;
  model: string;
  usage: Usage;
  /** The SDK's cost of the run in cents, when it reported one. */
  costCents?: number;
  durationMs: number;
  files: ChangedFile[];
}

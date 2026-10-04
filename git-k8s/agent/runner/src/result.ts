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
  /**
   * The run's model token cost in cents before discounts, the SDK's
   * rawCostCents, when it reported one. It's 0 for usage priced by request.
   */
  costCents?: number;
  /**
   * What Cursor charged for the run in cents, with discounts and fees, the
   * SDK's chargedCents. It's 0 for usage that a plan includes.
   */
  chargedCents?: number;
  durationMs: number;
  files: ChangedFile[];
  /**
   * Why the run failed after the agent started. Then verdict is fail,
   * summary, reasoning, and files are empty, and usage and the costs are
   * what the agent used before it failed.
   */
  error?: string;
}

export type TokenUsage = {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens?: number;
  cacheWriteTokens?: number;
  totalTokens: number;
};

/** A reply from the advisor for one request. */
export type Advice = {
  text: string;
  usage?: TokenUsage;
};

/** The advisor model, wrapped so the loop can run against a fake in tests. */
export type Advisor = {
  advise(prompt: string): Promise<Advice>;
  getBilledUsage?(): Promise<{ usage: TokenUsage; rawCostCents?: number }>;
  dispose(): Promise<void>;
};

/** One read of the game pane. `ok: false` means the pane is gone for good. */
export type Capture =
  | { ok: true; screen: string; dead: boolean }
  | { ok: false };

/** On-demand requests the player triggered with the hotkeys. */
export type Controls = {
  ask: boolean;
  toggle: boolean;
};

/** What the sidebar shows right now. */
export type SidebarView = {
  status: "watching" | "thinking" | "paused" | "over";
  auto: boolean;
  advice: string;
  note?: string;
  tokens: number;
  costCents?: number;
};

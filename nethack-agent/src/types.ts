export type ExitReason = "process_ended" | "agent_quit" | "turn_cap" | "error";

export type TokenUsage = {
  inputTokens: number;
  outputTokens: number;
  cacheReadTokens?: number;
  cacheWriteTokens?: number;
  reasoningTokens?: number;
  totalTokens: number;
};

export type TraceMessage = {
  type: "thinking" | "assistant" | "tool_call";
  text?: string;
  name?: string;
  status?: string;
  args?: unknown;
  result?: unknown;
};

export type Note = {
  id: string;
  life: number;
  turn: number;
  text: string;
  retracted: boolean;
};

export type Procedure = {
  name: string;
  keys: string;
  life: number;
  turn: number;
};

export type Ending = {
  life: number;
  turns: number;
  exitReason: ExitReason;
  screen: string;
};

export type Memory = {
  notes: Note[];
  procedures: Procedure[];
  endings: Ending[];
  nextNote: number;
};

export type AgentAction = {
  keys: string;
  quit: boolean;
  note?: string;
  retract?: string;
  save?: { name: string; keys: string };
  run?: string;
};

export type Observation = {
  screen: string;
  ended: boolean;
};

export type LifeTurn = {
  turn: number;
  prompt: string;
  rawText: string;
  action: AgentAction | null;
  parseError?: string;
  sentKeys: string;
  screenAfter: string;
  ack?: string;
  tokens?: number;
  usage?: TokenUsage;
};

export type LifeRecord = {
  life: number;
  turns: number;
  exitReason: ExitReason;
  finalScreen: string;
  actions: LifeTurn[];
  debrief?: LifeTurn;
  error?: string;
  /** Set when this life asked the SDK for a cost. False means the SDK had not reported one yet. */
  costReported?: boolean;
  billedCostCents?: number;
  invoiceCents?: number;
  tokens?: TokenUsage;
};

export type RunRecord = {
  id: string;
  startedAt: string;
  finishedAt: string;
  backend: "mock" | "cursor";
  game: "fake" | "tty";
  model: string;
  seed: number;
  lives: LifeRecord[];
  memory: Memory;
  usage: {
    inputTokens: number;
    outputTokens: number;
    cacheReadTokens: number;
    cacheWriteTokens: number;
    totalTokens: number;
    /** SDK raw token cost, in cents. Present only when `costReported` is true. */
    totalRawCostCents?: number;
    invoiceCents?: number;
    costReported: boolean;
  };
};

import type {
  AgentFactory,
  AgentFactoryOptions,
  PlayerAgent,
  PromptTurn,
  TurnResult,
} from "./types.js";

/**
 * Deterministic in-process agent for unit tests and --backend mock dry runs.
 * Does not call the Cursor SDK or spend tokens.
 */
export const createMockAgent: AgentFactory = async (options) => {
  const script = options.script ?? defaultScript(options);
  let index = 0;

  const agent: PlayerAgent = {
    role: options.role,
    model: `mock:${options.model}`,
    async turn(_input: PromptTurn): Promise<TurnResult> {
      const started = Date.now();
      if (index >= script.turns.length) {
        throw new Error(
          `Mock ${options.role} has no scripted turn at index ${index}`,
        );
      }
      const step = script.turns[index++]!;
      if (step.commitSecret) {
        if (!options.allowCommitSecret) {
          throw new Error("Mock tried to commit_secret without permission");
        }
        options.onCommitSecret?.(step.commitSecret);
      }

      return {
        public: { text: step.text, thinking: step.thinking ?? "" },
        rawText: step.text,
        toolNames: step.commitSecret ? ["commit_secret"] : [],
        committedSecret: step.commitSecret,
        usage: {
          inputTokens: 100 + index * 10,
          outputTokens: 50 + index * 5,
          totalTokens: 150 + index * 15,
        },
        durationMs: Math.max(1, Date.now() - started),
      };
    },
    async getBilledUsage() {
      return { totalTokens: 0, rawCostCents: 0 };
    },
    async dispose() {
      /* no-op */
    },
  };

  void options.systemPrompt;
  return agent;
};

function defaultScript(options: AgentFactoryOptions) {
  if (options.role === "keeper") {
    return {
      turns: [
        {
          thinking: "I will pick something other than a shark.",
          text: [
            "Secret committed. First clue: it is a mammal that lives in the ocean.",
            '```json\n{"type":"clue","text":"it is a mammal that lives in the ocean"}\n```',
          ].join("\n"),
          commitSecret: "dolphin",
        },
        {
          thinking: "Stay vague but fair.",
          text: [
            "Clue: it is known for being playful and intelligent.",
            '```json\n{"type":"clue","text":"it is known for being playful and intelligent"}\n```',
          ].join("\n"),
        },
      ],
    };
  }
  return {
    turns: [
      {
        thinking: "Ocean mammal... maybe whale?",
        text: 'Is it a whale?\n```json\n{"type":"guess","value":"whale"}\n```',
      },
      {
        thinking: "Playful ocean mammal — dolphin.",
        text: 'I think it is a dolphin.\n```json\n{"type":"guess","value":"dolphin"}\n```',
      },
    ],
  };
}

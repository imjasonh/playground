import type {
  AgentFactory,
  AgentFactoryOptions,
  MockScript,
  PlayerAgent,
  PromptTurn,
  TurnResult,
} from "./types.js";
import type { TraceMessage } from "../types.js";

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
      const step =
        index < script.turns.length
          ? script.turns[index]!
          : fallbackStep(options.role, index);
      index++;

      const messages: TraceMessage[] = [];
      if (step.thinking) {
        messages.push({ type: "thinking", text: step.thinking });
      }
      for (const call of step.toolCalls ?? []) {
        messages.push({
          type: "tool_call",
          name: call.name,
          status: call.status ?? "completed",
          args: call.args,
          result: call.result,
        });
      }
      messages.push({ type: "assistant", text: step.text });

      return {
        public: { messages },
        rawText: step.text,
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

function fallbackStep(
  role: "knower" | "guesser",
  index: number,
): MockScript["turns"][number] {
  if (role === "guesser") {
    return {
      thinking: "Out of ideas.",
      text: `\`\`\`json\n{"type":"give_up","reason":"mock script exhausted at turn ${index}"}\n\`\`\``,
    };
  }
  return {
    thinking: "Another vague clue.",
    text: `\`\`\`json\n{"type":"clue","text":"mock filler clue ${index}"}\n\`\`\``,
  };
}

function defaultScript(options: AgentFactoryOptions): MockScript {
  if (options.role === "knower") {
    return {
      turns: [
        {
          thinking: "I'll pick dolphin as the secret.",
          text: '```json\n{"type":"commit","secret":"dolphin"}\n```',
        },
        {
          thinking: "I will stay vague.",
          text: [
            "First clue: it is a mammal that lives in the ocean.",
            '```json\n{"type":"clue","text":"it is a mammal that lives in the ocean"}\n```',
          ].join("\n"),
        },
        {
          thinking: "Still safe.",
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

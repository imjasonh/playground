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
    thinking: "Another shared fact.",
    text: `\`\`\`json\n{"type":"shared_fact","text":"mock shared fact ${index}"}\n\`\`\``,
  };
}

function defaultScript(options: AgentFactoryOptions): MockScript {
  if (options.role === "knower") {
    return {
      turns: [
        {
          thinking: "I'll pick Jaws... wait, better pick something else. Finding Nemo.",
          text: '```json\n{"type":"commit","secret":"Finding Nemo"}\n```',
        },
        {
          thinking: "They guessed Titanic. Shared: widely known, family-ish? Better: ocean setting.",
          text: [
            "Both are set primarily in or on the ocean.",
            '```json\n{"type":"shared_fact","text":"set primarily in or on the ocean"}\n```',
          ].join("\n"),
        },
        {
          thinking: "They guessed The Perfect Storm. Shared: animated? No — family film? Pixar.",
          text: [
            "Both feature a parent-child relationship as a central plot.",
            '```json\n{"type":"shared_fact","text":"central parent-child relationship"}\n```',
          ].join("\n"),
        },
      ],
    };
  }
  return {
    turns: [
      {
        thinking: "Cold open — try a famous movie.",
        text: 'Is it Titanic?\n```json\n{"type":"guess","value":"Titanic"}\n```',
      },
      {
        thinking: "Ocean setting... The Perfect Storm?",
        text: '```json\n{"type":"guess","value":"The Perfect Storm"}\n```',
      },
      {
        thinking: "Ocean + parent-child — Finding Nemo.",
        text: '```json\n{"type":"guess","value":"Finding Nemo"}\n```',
      },
    ],
  };
}

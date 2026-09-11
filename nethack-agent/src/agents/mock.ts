import type { AgentFactory, PlayerAgent, PromptTurn, TurnResult } from "./types.js";

export const createMockAgent: AgentFactory = async (options) => {
  const script = options.script ?? { turns: [] };
  let index = 0;

  const player: PlayerAgent = {
    model: options.model,
    async turn(input: PromptTurn): Promise<TurnResult> {
      script.seenPrompts?.push(input.prompt);
      const next = script.turns[index];
      index += 1;
      const text = next?.text ?? '{"quit":true}';
      return {
        rawText: text,
        messages: [
          ...(next?.thinking
            ? [{ type: "thinking" as const, text: next.thinking }]
            : []),
          { type: "assistant", text },
        ],
        durationMs: 1,
      };
    },
    async dispose() {
      // Nothing to close.
    },
  };
  return player;
};

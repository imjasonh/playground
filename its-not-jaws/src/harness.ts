import { randomUUID } from "node:crypto";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { createCursorAgent } from "./agents/cursor.js";
import { createMockAgent } from "./agents/mock.js";
import type { AgentFactory, MockScript, PlayerAgent } from "./agents/types.js";
import { getGame } from "./games/stub.js";
import { judge } from "./judge.js";
import { parseMove } from "./protocol.js";
import {
  guesserPromptFromKeeper,
  guesserSystemPrompt,
  keeperOpeningPrompt,
  keeperPromptFromGuesser,
  keeperSystemPrompt,
} from "./prompts.js";
import type {
  AgentTurn,
  GameRecord,
  HarnessConfig,
  PlayerUsage,
  TokenUsage,
} from "./types.js";

export type RunGameOptions = HarnessConfig & {
  /** Override factories (tests). */
  factories?: { mock?: AgentFactory; cursor?: AgentFactory };
  keeperScript?: MockScript;
  guesserScript?: MockScript;
  /** Skip writing results JSON. */
  dryRun?: boolean;
};

export async function runGame(options: RunGameOptions): Promise<GameRecord> {
  const game = getGame(options.gameId);
  const id = randomUUID();
  const startedAt = new Date().toISOString();
  const secret = options.secret ?? game.pickSecret(options.seed);

  const factory: AgentFactory =
    options.backend === "mock"
      ? (options.factories?.mock ?? createMockAgent)
      : (options.factories?.cursor ?? createCursorAgent);

  const keeperWorkspace = path.join(options.workspacesRoot, id, "keeper");
  const guesserWorkspace = path.join(options.workspacesRoot, id, "guesser");

  const keeper = await factory({
    role: "keeper",
    model: options.keeperModel,
    systemPrompt: keeperSystemPrompt(game, secret),
    workspaceDir: keeperWorkspace,
    apiKey: options.apiKey,
    seed: options.seed,
    script: options.keeperScript,
  });

  const guesser = await factory({
    role: "guesser",
    model: options.guesserModel,
    systemPrompt: guesserSystemPrompt(game),
    workspaceDir: guesserWorkspace,
    apiKey: options.apiKey,
    seed: options.seed,
    script: options.guesserScript,
  });

  const turns: AgentTurn[] = [];
  let hitMaxTurns = false;
  let stop = false;

  try {
    turns.push(await playTurn(keeper, keeperOpeningPrompt(), turns.length));

    let round = 1;
    while (!stop && round <= options.maxTurns) {
      const lastKeeper = lastTurn(turns, "keeper");
      if (!lastKeeper) break;

      const guessTurn = await playTurn(
        guesser,
        guesserPromptFromKeeper(lastKeeper.public, round),
        turns.length,
      );
      turns.push(guessTurn);

      if (guessTurn.move?.type === "give_up") {
        stop = true;
        break;
      }
      if (
        guessTurn.move?.type === "guess" &&
        normalizeEq(guessTurn.move.value, secret)
      ) {
        stop = true;
        break;
      }

      if (round >= options.maxTurns) {
        hitMaxTurns = true;
        stop = true;
        break;
      }

      turns.push(
        await playTurn(
          keeper,
          keeperPromptFromGuesser(guessTurn.public, round),
          turns.length,
        ),
      );
      round++;
    }

    if (
      !stop &&
      turns.filter((t) => t.role === "guesser").length >= options.maxTurns
    ) {
      hitMaxTurns = true;
    }
  } finally {
    await Promise.allSettled([keeper.dispose(), guesser.dispose()]);
  }

  const outcome = judge({
    game,
    secret,
    turns,
    hitMaxTurns,
  });

  const keeperUsage = await finalizeUsage(keeper, "keeper", turns);
  const guesserUsage = await finalizeUsage(guesser, "guesser", turns);

  const finishedAt = new Date().toISOString();
  const record: GameRecord = {
    id,
    game: game.id,
    startedAt,
    finishedAt,
    keeperModel: keeper.model,
    guesserModel: guesser.model,
    backend: options.backend,
    secret,
    turns,
    outcome,
    usage: {
      keeper: keeperUsage,
      guesser: guesserUsage,
      totalTokens:
        keeperUsage.tokens.totalTokens + guesserUsage.tokens.totalTokens,
      totalRawCostCents: sumOptional(
        keeperUsage.cost?.rawCostCents,
        guesserUsage.cost?.rawCostCents,
      ),
    },
    gameLength: turns.filter((t) => t.role === "guesser").length,
  };

  if (!options.dryRun) {
    await mkdir(options.resultsDir, { recursive: true });
    const outPath = path.join(options.resultsDir, `${id}.json`);
    await writeFile(outPath, JSON.stringify(record, null, 2), "utf8");
    if (options.verbose) {
      console.error(`Wrote ${outPath}`);
    }
  }

  return record;
}

async function playTurn(
  agent: PlayerAgent,
  prompt: string,
  turnIndex: number,
): Promise<AgentTurn> {
  const result = await agent.turn({ prompt });
  return {
    role: agent.role,
    turnIndex,
    durationMs: result.durationMs,
    public: result.public,
    usage: result.usage,
    move: parseMove(result.rawText),
    rawText: result.rawText,
  };
}

function lastTurn(
  turns: AgentTurn[],
  role: "keeper" | "guesser",
): AgentTurn | undefined {
  for (let i = turns.length - 1; i >= 0; i--) {
    if (turns[i]!.role === role) return turns[i];
  }
  return undefined;
}

function normalizeEq(a: string, b: string): boolean {
  return (
    a.trim().toLowerCase().replace(/\s+/g, " ") ===
    b.trim().toLowerCase().replace(/\s+/g, " ")
  );
}

async function finalizeUsage(
  agent: PlayerAgent,
  role: "keeper" | "guesser",
  turns: AgentTurn[],
): Promise<PlayerUsage> {
  const summed = sumTokens(
    turns.filter((t) => t.role === role).map((t) => t.usage),
  );
  let cost: PlayerUsage["cost"];
  if (agent.getBilledUsage) {
    const billed = await agent.getBilledUsage();
    if (billed.rawCostCents || billed.totalTokens) {
      cost = { rawCostCents: billed.rawCostCents };
      if (!summed.totalTokens && billed.totalTokens) {
        summed.totalTokens = billed.totalTokens;
      }
    }
  }
  return {
    role,
    model: agent.model,
    tokens: summed,
    cost,
    turns: turns.filter((t) => t.role === role).length,
  };
}

function sumTokens(parts: Array<TokenUsage | undefined>): TokenUsage {
  const out: TokenUsage = {
    inputTokens: 0,
    outputTokens: 0,
    cacheReadTokens: 0,
    cacheWriteTokens: 0,
    reasoningTokens: 0,
    totalTokens: 0,
  };
  for (const p of parts) {
    if (!p) continue;
    out.inputTokens += p.inputTokens;
    out.outputTokens += p.outputTokens;
    out.cacheReadTokens! += p.cacheReadTokens ?? 0;
    out.cacheWriteTokens! += p.cacheWriteTokens ?? 0;
    out.reasoningTokens! += p.reasoningTokens ?? 0;
    out.totalTokens += p.totalTokens;
  }
  return out;
}

function sumOptional(a?: number, b?: number): number | undefined {
  if (a == null && b == null) return undefined;
  return (a ?? 0) + (b ?? 0);
}

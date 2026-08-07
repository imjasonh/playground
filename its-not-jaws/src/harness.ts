import { randomUUID } from "node:crypto";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { createCursorAgent } from "./agents/cursor.js";
import { createMockAgent } from "./agents/mock.js";
import type { AgentFactory, MockScript, PlayerAgent } from "./agents/types.js";
import { formatGameHtml } from "./format-html.js";
import { getGame } from "./games/its-not-jaws.js";
import { judge } from "./judge.js";
import { parseMove } from "./protocol.js";
import {
  guesserOpeningPrompt,
  guesserPromptFromKnower,
  guesserSystemPrompt,
  knowerPromptFromGuesser,
  knowerSetupPrompt,
  knowerSystemPrompt,
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
  knowerScript?: MockScript;
  guesserScript?: MockScript;
  /** Skip writing results JSON. */
  dryRun?: boolean;
};

export async function runGame(options: RunGameOptions): Promise<GameRecord> {
  const game = getGame(options.gameId);
  const id = randomUUID();
  const startedAt = new Date().toISOString();

  const factory: AgentFactory =
    options.backend === "mock"
      ? (options.factories?.mock ?? createMockAgent)
      : (options.factories?.cursor ?? createCursorAgent);

  const knowerWorkspace = path.join(options.workspacesRoot, id, "knower");
  const guesserWorkspace = path.join(options.workspacesRoot, id, "guesser");

  const knower = await factory({
    role: "knower",
    model: options.knowerModel,
    systemPrompt: knowerSystemPrompt(game),
    workspaceDir: knowerWorkspace,
    apiKey: options.apiKey,
    seed: options.seed,
    script: options.knowerScript,
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
  const sharedFacts: string[] = [];
  let secret: string | undefined;
  let secretCommitted = false;
  let hitMaxTurns = false;
  let stop = false;

  try {
    // Private setup: knower picks + commits. Never forwarded to the guesser.
    const setup = await playTurn(
      knower,
      knowerSetupPrompt(),
      turns.length,
      "setup",
    );
    turns.push(setup);
    if (setup.move?.type === "commit") {
      secret = setup.move.secret;
      secretCommitted = true;
    } else {
      stop = true;
    }

    // Guesser moves first (no free opening clue from the knower).
    let round = 1;
    while (!stop && round <= options.maxTurns) {
      let guessPrompt = guesserOpeningPrompt();
      if (round > 1) {
        const lastKnower = lastPlayTurn(turns, "knower");
        if (!lastKnower) {
          stop = true;
          break;
        }
        guessPrompt = guesserPromptFromKnower(
          lastKnower.public,
          round,
          sharedFacts,
        );
      }

      const guessTurn = await playTurn(
        guesser,
        guessPrompt,
        turns.length,
        "play",
      );
      turns.push(guessTurn);

      if (guessTurn.move?.type === "give_up") {
        stop = true;
        break;
      }

      const guessValue =
        guessTurn.move?.type === "guess" ? guessTurn.move.value : undefined;

      if (guessValue && secret && normalizeEq(guessValue, secret)) {
        stop = true;
        break;
      }

      if (round >= options.maxTurns) {
        hitMaxTurns = true;
        stop = true;
        break;
      }

      if (!guessValue) {
        // No parseable guess — end the loop; judge will classify from the transcript.
        stop = true;
        break;
      }

      const factTurn = await playTurn(
        knower,
        knowerPromptFromGuesser(guessTurn.public, guessValue, round),
        turns.length,
        "play",
      );
      turns.push(factTurn);
      if (factTurn.move?.type === "shared_fact") {
        sharedFacts.push(factTurn.move.text);
      }
      round++;
    }

    if (
      !stop &&
      turns.filter((t) => t.role === "guesser").length >= options.maxTurns
    ) {
      hitMaxTurns = true;
    }
  } finally {
    await Promise.allSettled([knower.dispose(), guesser.dispose()]);
  }

  const outcome = judge({
    game,
    secret,
    secretCommitted,
    turns,
    hitMaxTurns,
  });

  const knowerUsage = await finalizeUsage(knower, "knower", turns);
  const guesserUsage = await finalizeUsage(guesser, "guesser", turns);

  const finishedAt = new Date().toISOString();
  const record: GameRecord = {
    id,
    game: game.id,
    startedAt,
    finishedAt,
    knowerModel: knower.model,
    guesserModel: guesser.model,
    backend: options.backend,
    secret,
    secretCommitted,
    turns,
    outcome,
    usage: {
      knower: knowerUsage,
      guesser: guesserUsage,
      totalTokens:
        knowerUsage.tokens.totalTokens + guesserUsage.tokens.totalTokens,
      totalRawCostCents: sumOptional(
        knowerUsage.cost?.rawCostCents,
        guesserUsage.cost?.rawCostCents,
      ),
    },
    gameLength: turns.filter((t) => t.role === "guesser").length,
  };

  if (!options.dryRun) {
    await mkdir(options.resultsDir, { recursive: true });
    const outPath = path.join(options.resultsDir, `${id}.json`);
    const htmlPath = path.join(options.resultsDir, `${id}.html`);
    await writeFile(outPath, JSON.stringify(record, null, 2), "utf8");
    await writeFile(htmlPath, formatGameHtml(record), "utf8");
    if (options.verbose) {
      console.error(`Wrote ${outPath}`);
      console.error(`Wrote ${htmlPath}`);
    }
  }

  return record;
}

async function playTurn(
  agent: PlayerAgent,
  prompt: string,
  turnIndex: number,
  phase: "setup" | "play",
): Promise<AgentTurn> {
  const result = await agent.turn({ prompt });
  return {
    role: agent.role,
    turnIndex,
    phase,
    durationMs: result.durationMs,
    public: result.public,
    usage: result.usage,
    move: parseMove(result.rawText),
    rawText: result.rawText,
  };
}

function lastPlayTurn(
  turns: AgentTurn[],
  role: "knower" | "guesser",
): AgentTurn | undefined {
  for (let i = turns.length - 1; i >= 0; i--) {
    const t = turns[i]!;
    if (t.role === role && t.phase === "play") return t;
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
  role: "knower" | "guesser",
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

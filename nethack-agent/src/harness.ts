import { randomUUID } from "node:crypto";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { createCursorAgent } from "./agents/cursor.js";
import { createMockAgent } from "./agents/mock.js";
import type { AgentFactory, MockScript, PlayerAgent } from "./agents/types.js";
import {
  addTokens,
  emptyTokens,
  foldUsageCost,
  formatLifeUsageCost,
  formatUsageCost,
} from "./cost.js";
import type { TokenTotals } from "./cost.js";
import { createFakeBackend } from "./games/fake.js";
import { createTtyBackend, type TtyOptions } from "./games/tty.js";
import type { Game, GameBackend } from "./games/types.js";
import { clampLives, clampMaxTurns } from "./limits.js";
import {
  applyNotebook,
  emptyMemory,
  loadMemory,
  lookupProcedure,
  recordEnding,
  saveMemory,
} from "./memory.js";
import { parseAction, screenDiff } from "./protocol.js";
import { debriefPrompt, playPrompt, retryPrompt, systemPrompt } from "./prompts.js";
import { assertLearningGame } from "./real-game.js";
import type {
  AgentAction,
  ExitReason,
  LifeRecord,
  LifeTurn,
  Memory,
  RunRecord,
  TokenUsage,
} from "./types.js";

export type RunOptions = {
  backend: "mock" | "cursor";
  game: "fake" | "tty";
  model: string;
  lives: number;
  maxTurns: number;
  seed: number;
  apiKey?: string;
  resultsDir: string;
  workspacesRoot: string;
  resumeMemoryDir?: string;
  /** Canonical notes from real nethack only. Refuses the fake screen. */
  notebookDir?: string;
  tty?: TtyOptions;
  verbose?: boolean;
  dryRun?: boolean;
  factories?: { mock?: AgentFactory; cursor?: AgentFactory };
  script?: MockScript;
};

export async function runSession(options: RunOptions): Promise<RunRecord> {
  if (options.notebookDir) assertLearningGame(options.game);
  const lives = clampLives(options.lives);
  const maxTurns = clampMaxTurns(options.maxTurns);
  const id = randomUUID();
  const startedAt = new Date().toISOString();
  const memory = options.resumeMemoryDir
    ? await loadMemory(options.resumeMemoryDir)
    : emptyMemory();
  const gameBackend = createBackend(options);
  const factory: AgentFactory =
    options.backend === "mock"
      ? (options.factories?.mock ?? createMockAgent)
      : (options.factories?.cursor ?? createCursorAgent);

  const lifeRecords: LifeRecord[] = [];

  for (let life = 1; life <= lives; life++) {
    const record = await playLife({
      life,
      maxTurns,
      seed: options.seed,
      model: options.model,
      memory,
      gameBackend,
      factory,
      script: options.script,
      apiKey: options.apiKey,
      workspaceDir: path.join(options.workspacesRoot, id, `life-${life}`),
      verbose: options.verbose,
    });
    lifeRecords.push(record);
    if (options.verbose) {
      console.error(
        `life ${life} ${record.exitReason} after ${record.turns} turns`,
      );
    }
  }

  const finishedAt = new Date().toISOString();
  const run: RunRecord = {
    id,
    startedAt,
    finishedAt,
    backend: options.backend,
    game: options.game,
    model: options.model,
    seed: options.seed,
    lives: lifeRecords,
    memory,
    usage: foldUsageCost(lifeRecords),
  };

  if (!options.dryRun) {
    const outDir = path.join(options.resultsDir, id);
    await mkdir(outDir, { recursive: true });
    await saveMemory(path.join(outDir, "memory"), memory);
    await writeFile(path.join(outDir, "record.json"), JSON.stringify(run, null, 2));
    await writeFile(path.join(outDir, "transcript.txt"), renderTranscript(run));
    if (options.notebookDir) {
      await saveMemory(options.notebookDir, memory);
    }
  }
  return run;
}

function createBackend(options: RunOptions): GameBackend {
  if (options.game === "tty") {
    return createTtyBackend(
      options.tty ?? { command: "nethack" },
    );
  }
  return createFakeBackend();
}

async function playLife(input: {
  life: number;
  maxTurns: number;
  seed: number;
  model: string;
  memory: Memory;
  gameBackend: GameBackend;
  factory: AgentFactory;
  script?: MockScript;
  apiKey?: string;
  workspaceDir: string;
  verbose?: boolean;
}): Promise<LifeRecord> {
  const actions: LifeTurn[] = [];
  let game: Game | undefined;
  let agent: PlayerAgent | undefined;
  let exitReason: ExitReason = "error";
  let finalScreen = "";
  let error: string | undefined;

  try {
    await mkdir(input.workspaceDir, { recursive: true });
    game = await input.gameBackend.start({
      lifeDir: input.workspaceDir,
      seed: input.seed,
    });
    agent = await input.factory({
      model: input.model,
      systemPrompt: systemPrompt(),
      workspaceDir: path.join(input.workspaceDir, "agent"),
      apiKey: input.apiKey,
      script: input.script,
    });

    let observation = await game.observe();
    finalScreen = observation.screen;
    let previousScreen = "";
    const pendingAcks: string[] = [];

    if (observation.ended) {
      exitReason = "process_ended";
    } else {
      for (let turn = 1; turn <= input.maxTurns; turn++) {
        const prompt = playPrompt({
          life: input.life,
          turn,
          screen: observation.screen,
          diff: previousScreen ? screenDiff(previousScreen, observation.screen) : "",
          memory: input.memory,
          includeMemory: turn === 1,
          acks: pendingAcks.splice(0),
        });
        const played = await takeAction(agent, prompt);
        let sentKeys = "";
        let ack = played.ack;

        if (played.action?.quit) {
          const notes = applyNotebook(input.memory, played.action, input.life, turn);
          ack = joinAck(ack, notes.join("\n"));
          actions.push({
            turn,
            prompt,
            rawText: played.rawText,
            action: played.action,
            parseError: played.parseError,
            sentKeys,
            screenAfter: observation.screen,
            ack,
            tokens: played.tokens,
            usage: played.usage,
          });
          exitReason = "agent_quit";
          break;
        }

        if (played.action && game) {
          // File sequences before running one, so a save and a run in the same
          // reply use the sequence the agent just wrote.
          const notes = applyNotebook(input.memory, played.action, input.life, turn);
          ack = joinAck(ack, notes.join("\n"));
          const keys = keysToSend(input.memory, played.action);
          if (keys.error) {
            ack = joinAck(ack, keys.error);
          } else if (keys.keys) {
            sentKeys = keys.keys;
            previousScreen = observation.screen;
            observation = await game.sendKeys(keys.keys);
            finalScreen = observation.screen;
          }
          if (ack) pendingAcks.push(ack);
        }

        actions.push({
          turn,
          prompt,
          rawText: played.rawText,
          action: played.action,
          parseError: played.parseError,
          sentKeys,
          screenAfter: observation.screen,
          ack,
          tokens: played.tokens,
          usage: played.usage,
        });

        if (observation.ended) {
          exitReason = "process_ended";
          break;
        }
        if (turn === input.maxTurns) {
          exitReason = "turn_cap";
        }
      }
    }

    if (exitReason === "agent_quit" || exitReason === "turn_cap") {
      await game.close();
      observation = await game.observe();
      finalScreen = observation.screen || finalScreen;
    }
  } catch (err) {
    error = err instanceof Error ? err.message : String(err);
    exitReason = "error";
  }

  let debrief: LifeTurn | undefined;
  let costReported: boolean | undefined;
  let billedCostCents: number | undefined;
  let invoiceCents: number | undefined;
  let billedTokens: TokenUsage | undefined;
  if (agent && finalScreen) {
    try {
      debrief = await runDebrief(agent, input.memory, input.life, actions.length, finalScreen);
    } catch (err) {
      error = joinAck(error, err instanceof Error ? err.message : String(err));
    }
  }
  if (agent?.getBilledUsage) {
    costReported = false;
    try {
      const billed = await agent.getBilledUsage();
      billedTokens = billed.usage;
      if (billed.rawCostCents !== undefined) {
        costReported = true;
        billedCostCents = billed.rawCostCents;
        invoiceCents = billed.chargedCents;
      }
    } catch {
      costReported = false;
    }
  }

  recordEnding(input.memory, {
    life: input.life,
    turns: actions.length,
    exitReason,
    screen: finalScreen,
  });

  await agent?.dispose().catch(() => undefined);
  await game?.close().catch(() => undefined);

  return {
    life: input.life,
    turns: actions.length,
    exitReason,
    finalScreen,
    actions,
    debrief,
    error,
    costReported,
    billedCostCents,
    invoiceCents,
    tokens: lifeTokens(actions, debrief, billedTokens),
  };
}

function keysToSend(
  memory: Memory,
  action: { keys: string; run?: string },
): { keys: string; error?: string } {
  if (action.run) {
    const procedure = lookupProcedure(memory, action.run);
    if (!procedure) return { keys: "", error: `unknown sequence ${action.run}` };
    return { keys: procedure.keys };
  }
  return { keys: action.keys };
}

async function takeAction(
  agent: PlayerAgent,
  prompt: string,
): Promise<{
  rawText: string;
  action: AgentAction | null;
  parseError?: string;
  ack?: string;
  tokens: number;
  usage?: TokenUsage;
}> {
  const first = await agent.turn({ prompt });
  const parsed = parseAction(first.rawText);
  if (parsed.ok) {
    return {
      rawText: first.rawText,
      action: parsed.action,
      tokens: first.usage?.totalTokens ?? 0,
      usage: first.usage,
    };
  }
  const retry = await agent.turn({
    prompt: `${prompt}\n\n${retryPrompt()}\n${parsed.error}`,
  });
  const again = parseAction(retry.rawText);
  const usage = addTokens(addTokens(emptyTokens(), first.usage), retry.usage);
  if (again.ok) {
    return { rawText: retry.rawText, action: again.action, tokens: usage.totalTokens, usage };
  }
  return {
    rawText: retry.rawText,
    action: null,
    parseError: again.error,
    ack: "unparsed reply, no keys sent",
    tokens: usage.totalTokens,
    usage,
  };
}

async function runDebrief(
  agent: PlayerAgent,
  memory: Memory,
  life: number,
  turn: number,
  screen: string,
): Promise<LifeTurn> {
  const prompt = debriefPrompt({ screen });
  const result = await agent.turn({ prompt });
  const parsed = parseAction(result.rawText);
  let ack: string | undefined;
  let action = parsed.ok ? parsed.action : null;
  if (action) {
    action = { ...action, keys: "", quit: false, run: undefined };
    const notes = applyNotebook(memory, action, life, turn);
    ack = notes.join("\n") || undefined;
  }
  return {
    turn,
    prompt,
    rawText: result.rawText,
    action,
    parseError: parsed.ok ? undefined : parsed.error,
    sentKeys: "",
    screenAfter: screen,
    ack,
    tokens: result.usage?.totalTokens ?? 0,
    usage: result.usage,
  };
}

function lifeTokens(
  actions: LifeTurn[],
  debrief: LifeTurn | undefined,
  billed: TokenUsage | undefined,
): TokenUsage {
  if (
    billed &&
    (billed.totalTokens > 0 || billed.inputTokens > 0 || billed.outputTokens > 0)
  ) {
    return billed;
  }
  let tokens: TokenTotals = emptyTokens();
  for (const turn of actions) tokens = addTokens(tokens, turn.usage);
  return addTokens(tokens, debrief?.usage);
}

function joinAck(left?: string, right?: string): string | undefined {
  const parts = [left, right].filter((part) => part && part.length > 0);
  return parts.length > 0 ? parts.join("\n") : undefined;
}

function renderTranscript(run: RunRecord): string {
  const chunks: string[] = [];
  chunks.push(
    `run ${run.id}`,
    `backend ${run.backend} game ${run.game} model ${run.model} seed ${run.seed}`,
    formatUsageCost(run.model, run.usage),
    "",
  );
  for (const life of run.lives) {
    chunks.push(`=== life ${life.life} ${life.exitReason} turns ${life.turns} ===`);
    const lifeCost = formatLifeUsageCost(life);
    if (lifeCost) chunks.push(lifeCost);
    if (life.error) chunks.push(`error: ${life.error}`);
    for (const turn of life.actions) {
      chunks.push(`--- turn ${turn.turn} ---`);
      if (turn.sentKeys) chunks.push(`sent ${JSON.stringify(turn.sentKeys)}`);
      if (turn.action?.note) chunks.push(`note ${turn.action.note}`);
      if (turn.action?.run) chunks.push(`run ${turn.action.run}`);
      if (turn.parseError) chunks.push(`parse ${turn.parseError}`);
      chunks.push(turn.screenAfter, "");
    }
    if (life.debrief?.action?.note) {
      chunks.push(`debrief note ${life.debrief.action.note}`, "");
    }
  }
  return chunks.join("\n");
}

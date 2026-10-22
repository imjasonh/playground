import { copyFile, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { settingsPrompt, settingsSystemPrompt } from "./prompts.js";
import { backupPath, parseSettingsReply, resolveRcSource, type RcSource } from "./settings.js";
import type { Advisor } from "./types.js";

export type SettingsArgs = {
  file?: string;
  ask?: string;
  write: boolean;
  output?: string;
};

export type SettingsDeps = {
  makeAdvisor: (system: string) => Promise<Advisor>;
  home: string;
  nethackoptions?: string;
  now: () => Date;
  log: (line: string) => void;
};

export type SettingsResult = {
  review: string;
  config?: string;
  wrote?: string;
  backup?: string;
  tokens: number;
  costCents?: number;
};

/**
 * Review the player's NetHack config and, when asked, write the suggestion back.
 * The advisor and environment are injected so the whole flow runs in tests
 * without the Cursor SDK.
 */
export async function runSettings(args: SettingsArgs, deps: SettingsDeps): Promise<SettingsResult> {
  const source = resolveRcSource({
    fileArg: args.file,
    nethackoptions: deps.nethackoptions,
    home: deps.home,
    exists: existsSync,
  });
  const loaded = await loadSource(source);

  const advisor = await deps.makeAdvisor(settingsSystemPrompt());
  let parsed: { review: string; config?: string };
  let tokens = 0;
  let costCents: number | undefined;
  try {
    const reply = await advisor.advise(
      settingsPrompt({ kind: loaded.kind, contents: loaded.contents, ask: args.ask }),
    );
    parsed = parseSettingsReply(reply.text);
    tokens = reply.usage?.totalTokens ?? 0;
    if (advisor.getBilledUsage) {
      const billed = await advisor.getBilledUsage().catch(() => undefined);
      if (billed) {
        costCents = billed.rawCostCents;
        if (!tokens) tokens = billed.usage.totalTokens;
      }
    }
  } finally {
    await advisor.dispose();
  }

  deps.log(parsed.review);

  const result: SettingsResult = { review: parsed.review, config: parsed.config, tokens, costCents };
  if (!args.write && !args.output) {
    if (parsed.config) deps.log(`\nSuggested .nethackrc (use --write to save it):\n\n${parsed.config}`);
    return result;
  }

  if (!parsed.config) throw new Error("the model did not return a config block, so there is nothing to write");
  const target = args.output ?? source.path;
  if (!target) throw new Error("no file to write to; pass --output <path>");

  if (!args.output && existsSync(target)) {
    const backup = backupPath(target, deps.now());
    await copyFile(target, backup);
    result.backup = backup;
    deps.log(`\nbacked up ${target} to ${backup}`);
  }
  await writeFile(target, `${parsed.config}\n`, "utf8");
  result.wrote = target;
  deps.log(`wrote ${target}`);
  return result;
}

async function loadSource(source: RcSource): Promise<{ kind: RcSource["kind"]; contents: string }> {
  if (source.kind === "inline") return { kind: "inline", contents: source.contents ?? "" };
  if (source.kind === "file" && source.path && existsSync(source.path)) {
    return { kind: "file", contents: await readFile(source.path, "utf8") };
  }
  return { kind: "none", contents: "" };
}

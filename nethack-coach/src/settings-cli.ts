#!/usr/bin/env node
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createCursorAdvisor } from "./cursor.js";
import { runSettings } from "./settings-run.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");

function argValue(args: string[], name: string): string | undefined {
  const idx = args.indexOf(name);
  return idx < 0 ? undefined : args[idx + 1];
}

const HELP = [
  "Usage: npm run settings -- [options] [question]",
  "",
  "Review and improve your NetHack .nethackrc with a Cursor agent.",
  "",
  "  --file <path>     config to read (default: NETHACKOPTIONS, else ~/.nethackrc)",
  "  --model <id>      model id (default: grok-4.6)",
  "  --write           back up the current config and write the suggestion to it",
  "  --output <path>   write the suggestion to a new file instead",
  "  --ask <question>  a specific question about your settings",
  "  --help            show this help",
  "",
  "Without --write or --output it only prints; your files are untouched.",
  "",
].join("\n");

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes("--help") || args.includes("-h")) {
    process.stdout.write(`${HELP}\n`);
    return;
  }
  if (!process.env.CURSOR_API_KEY) throw new Error("CURSOR_API_KEY is required (https://cursor.com/dashboard/api)");

  const model = argValue(args, "--model") ?? "grok-4.6";
  const result = await runSettings(
    {
      file: argValue(args, "--file"),
      ask: argValue(args, "--ask") ?? freeText(args),
      write: args.includes("--write"),
      output: argValue(args, "--output"),
    },
    {
      makeAdvisor: (system) =>
        createCursorAdvisor({
          model,
          system,
          workspaceDir: path.join(root, ".workspace"),
          apiKey: process.env.CURSOR_API_KEY,
        }),
      home: os.homedir(),
      nethackoptions: process.env.NETHACKOPTIONS,
      now: () => new Date(),
      log: (line) => process.stdout.write(`${line}\n`),
    },
  );

  const cost = result.costCents !== undefined ? `  $${(result.costCents / 100).toFixed(2)}` : "";
  process.stdout.write(`\n${result.tokens.toLocaleString("en-US")} tokens${cost} (${model})\n`);
}

/** Trailing words that are not a flag or a flag's value become the question. */
function freeText(args: string[]): string | undefined {
  const flagsWithValue = new Set(["--file", "--model", "--output", "--ask"]);
  const words: string[] = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg.startsWith("--")) {
      if (flagsWithValue.has(arg)) i++;
      continue;
    }
    words.push(arg);
  }
  const text = words.join(" ").trim();
  return text || undefined;
}

main().catch((err) => {
  process.stderr.write(`${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
});

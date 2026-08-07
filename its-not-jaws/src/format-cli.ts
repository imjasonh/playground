#!/usr/bin/env node
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { formatGameHtml } from "./format-html.js";
import { extractGuesserLeakReport } from "./guesser-leak-report.js";
import { coalesceTraceMessages } from "./trace.js";
import type { GameRecord } from "./types.js";

async function main(): Promise<void> {
  const input = process.argv[2];
  if (!input || input === "--help" || input === "-h") {
    console.log(`Usage: npm run format -- <result.json> [out.html]

Render a game record JSON file as a readable chat HTML transcript.
If out.html is omitted, writes alongside the JSON with a .html suffix.
Also coalesces stream segments for older records.`);
    process.exit(input ? 0 : 1);
  }

  const abs = path.resolve(input);
  const record = JSON.parse(await readFile(abs, "utf8")) as GameRecord;
  for (const turn of record.turns ?? []) {
    turn.public.messages = coalesceTraceMessages(turn.public.messages ?? []);
  }
  if (!record.guesserLeakReport) {
    record.guesserLeakReport = extractGuesserLeakReport(
      record.turns ?? [],
      record.secret,
    );
  }
  const out =
    process.argv[3] != null
      ? path.resolve(process.argv[3])
      : abs.replace(/\.json$/i, ".html");
  await writeFile(out, formatGameHtml(record), "utf8");
  console.log(out);
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});

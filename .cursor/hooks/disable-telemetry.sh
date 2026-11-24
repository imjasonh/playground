#!/usr/bin/env bash
# preToolUse hook for Shell calls (see .cursor/hooks.json). The
# modern-web-guidance CLI sends usage data to Google unless
# DISABLE_TELEMETRY=1 is set, and a repository can't set environment
# variables for Cloud Agents, so this exports it ahead of any command
# that mentions the CLI.
set -euo pipefail

input=$(cat)
if [[ "$input" != *modern-web-guidance* ]]; then
  echo '{"permission":"allow"}'
  exit 0
fi

node -e '
const event = JSON.parse(require("node:fs").readFileSync(0, "utf8"));
const toolInput = event.tool_input ?? {};
const command = toolInput.command ?? "";
const out = {permission: "allow"};
if (!command.includes("DISABLE_TELEMETRY=1")) {
  out.updated_input = {...toolInput, command: `export DISABLE_TELEMETRY=1; ${command}`};
}
process.stdout.write(JSON.stringify(out));
' <<<"$input"

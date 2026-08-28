#!/usr/bin/env bash
# Kick an in-Worker load test and print the JSON report.
#
#   GIT_SERVER_URL=https://git.<account>.workers.dev ./scripts/loadtest-remote.sh
#
# Tunables (env):
#   BUDGET_USD=0.25       hard spend cap (marginal R2/DO/KV)
#   DURATION_SECS=15      per-stage wall time
#   SHARDS=1              in-process concurrency partitions
#   REPO=lt-<timestamp>   target repo (created/seeded if empty)
#
# See docs/api.md → POST /api/<repo>/loadtest and docs/loadtest-scaling.md.

set -euo pipefail
cd "$(dirname "$0")/.."

if [ -z "${GIT_SERVER_URL:-}" ]; then
  echo "set GIT_SERVER_URL to a deployed (or wrangler-dev) git-server" >&2
  exit 1
fi

BUDGET_USD="${BUDGET_USD:-0.25}"
DURATION_SECS="${DURATION_SECS:-15}"
SHARDS="${SHARDS:-1}"
REPO="${REPO:-lt-$(date +%s)-$RANDOM}"
URL="$GIT_SERVER_URL/api/$REPO/loadtest"

BODY=$(cat <<EOF
{
  "confirm": true,
  "budget_usd": $BUDGET_USD,
  "duration_secs": $DURATION_SECS,
  "shards": $SHARDS,
  "stages": [
    {"writers": 8, "readers": 0},
    {"writers": 32, "readers": 0},
    {"writers": 0, "readers": 64},
    {"writers": 8, "readers": 32}
  ]
}
EOF
)

echo "==> POST $URL"
echo "    budget=\$$BUDGET_USD duration=${DURATION_SECS}s shards=$SHARDS"
echo

curl -sS -X POST "$URL" \
  -H 'content-type: application/json' \
  -d "$BODY" | if command -v jq >/dev/null; then jq .; else cat; fi

echo
echo "NOTE: inspect Workers Traces / logs for git.loadtest + per-op spans."
echo "      Repo '$REPO' remains on the server."

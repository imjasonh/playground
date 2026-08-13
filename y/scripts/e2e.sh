#!/usr/bin/env bash
# End-to-end smoke of the y Worker under wrangler/miniflare (workerd).
#
#   ./scripts/e2e.sh              # build wasm, wrangler dev, hit HTTP
#   Y_URL=https://... ./scripts/e2e.sh
#                                 # against an already-running backend
#
# Local mode needs node/npx, the wasm32 target, and worker-build 0.8.5.
# It swaps in a temporary .dev.vars (restored on exit) and applies D1
# migrations to an isolated persist directory.
set -euo pipefail
cd "$(dirname "$0")/.."

WRANGLER_PID=""
TMP="$(mktemp -d)"
SAVED_DEV_VARS=""
cleanup() {
  [ -n "$WRANGLER_PID" ] && kill "$WRANGLER_PID" 2>/dev/null || true
  if [ -n "$SAVED_DEV_VARS" ]; then
    mv "$SAVED_DEV_VARS" .dev.vars
  elif [ -f .dev.vars ] && [ -f "$TMP/wrote-dev-vars" ]; then
    rm -f .dev.vars
  fi
  rm -rf "$TMP"
}
trap cleanup EXIT

fail() { echo "FAIL: $1" >&2; exit 1; }

if [ -z "${Y_URL:-}" ]; then
  echo "==> building Worker and starting wrangler dev"
  PORT="${PORT:-8788}"
  HASH="$(cargo run --quiet --example hash-password -- 'e2e-pass')"
  if [ -f .dev.vars ]; then
    SAVED_DEV_VARS="$TMP/dev.vars.bak"
    cp .dev.vars "$SAVED_DEV_VARS"
  fi
  cat > .dev.vars <<EOF
ADMIN_PASSWORD_HASH=${HASH}
SESSION_SECRET=e2e-session-secret-32b
EOF
  touch "$TMP/wrote-dev-vars"

  worker-build --release >/dev/null

  npx -y wrangler@4.107.0 d1 migrations apply y --local --persist-to "$TMP/state" >/dev/null
  npx -y wrangler@4.107.0 dev --port "$PORT" --local --persist-to "$TMP/state" \
    >"$TMP/wrangler.log" 2>&1 &
  WRANGLER_PID=$!
  Y_URL="http://127.0.0.1:${PORT}"

  echo "==> waiting for wrangler dev"
  for i in $(seq 1 90); do
    if curl -fsS "$Y_URL/" >/dev/null 2>&1; then break; fi
    if ! kill -0 "$WRANGLER_PID" 2>/dev/null; then
      echo "wrangler dev exited early:"; tail -50 "$TMP/wrangler.log"; exit 1
    fi
    sleep 1
    [ "$i" = 90 ] && { echo "wrangler dev never became ready"; tail -50 "$TMP/wrangler.log"; exit 1; }
  done
fi

ORIGIN="$Y_URL"
curl_h() { curl -sS -D "$TMP/hdr" -o "$TMP/body" "$@"; }
status() { awk 'NR==1 { print $2 }' "$TMP/hdr"; }
has_header() { grep -qi "^$1: $2" "$TMP/hdr"; }

echo "==> GET /"
curl_h "$Y_URL/"
[ "$(status)" = "200" ] || fail "GET / -> $(status)"
has_header "x-content-type-options" "nosniff" || fail "missing nosniff"
grep -q "No posts yet." "$TMP/body" || grep -q "class=\"post\"" "$TMP/body" || fail "home body"
echo "ok: home"

echo "==> GET /feed.xml"
curl_h "$Y_URL/feed.xml"
[ "$(status)" = "200" ] || fail "feed $(status)"
grep -q "<rss" "$TMP/body" || fail "rss body"
echo "ok: rss"

echo "==> image allowlist"
curl_h "$Y_URL/img/not-a-valid-key"
[ "$(status)" = "404" ] || fail "bad image key $(status)"
curl_h "$Y_URL/img/assets/paperclip.png"
[ "$(status)" = "200" ] || fail "paperclip $(status)"
echo "ok: images"

echo "==> subscribe CSRF + upsert"
curl_h -X POST -d "email=e2e@example.com" "$Y_URL/subscribe"
[ "$(status)" = "403" ] || fail "subscribe without origin $(status)"
curl_h -H "Origin: https://evil.example" -d "email=e2e@example.com" "$Y_URL/subscribe"
[ "$(status)" = "403" ] || fail "subscribe evil origin $(status)"
curl_h -H "Origin: ${ORIGIN}" -d "email=e2e@example.com" "$Y_URL/subscribe"
[ "$(status)" = "200" ] || fail "subscribe ok $(status)"
curl_h -H "Origin: ${ORIGIN}" -d "email=e2e@example.com" "$Y_URL/subscribe"
[ "$(status)" = "200" ] || fail "subscribe duplicate $(status)"
echo "ok: subscribe"

echo "==> bootstrap login + unicode post"
curl_h -c "$TMP/cookies" -H "Origin: ${ORIGIN}" \
  -d "password=e2e-pass" "$Y_URL/admin/login"
[ "$(status)" = "302" ] || fail "login $(status)"
curl_h -b "$TMP/cookies" -c "$TMP/cookies" -H "Origin: ${ORIGIN}" \
  -F "body=see 😀 https://youtu.be/dQw4w9wgGcQ" \
  "$Y_URL/admin/posts"
[ "$(status)" = "302" ] || fail "create post $(status)"
curl_h "$Y_URL/"
[ "$(status)" = "200" ] || fail "home after unicode post $(status)"
grep -q "youtube-nocookie.com/embed/dQw4w9wgGcQ" "$TMP/body" || fail "youtube embed missing"
echo "ok: unicode youtube render"

echo
echo "ALL E2E CHECKS PASSED against $Y_URL"

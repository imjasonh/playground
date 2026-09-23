#!/usr/bin/env bash
# Fetch the GitHub-hosted Laya multilingual int8 ONNX bundle.
# Hugging Face is not reachable from this environment.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEST="${LAYA_MODEL_DIR:-$ROOT/.laya-cache}"
BASE="${LAYA_BUNDLE_BASE:-https://raw.githubusercontent.com/koteitan/laya-int8/main}"
EXPECT_SIZE="${LAYA_ONNX_SIZE:-324983479}"

mkdir -p "$DEST/tokenizer"
cd "$DEST"

if [[ ! -f model.onnx ]] || [[ "$(stat -c%s model.onnx)" -ne "$EXPECT_SIZE" ]]; then
  for part in 000 001 002 003; do
    if [[ ! -f "model.onnx.$part" ]]; then
      curl -fL --retry 4 --retry-delay 4 -o "model.onnx.$part" "$BASE/model.onnx.$part"
    fi
  done
  cat model.onnx.000 model.onnx.001 model.onnx.002 model.onnx.003 > model.onnx
fi

if [[ "$(stat -c%s model.onnx)" -ne "$EXPECT_SIZE" ]]; then
  echo "laya bundle size $(stat -c%s model.onnx), expected $EXPECT_SIZE" >&2
  exit 1
fi

for rel in onnx_config.json rl_agent_config.json tokenizer/tokenizer.json tokenizer/tokenizer_config.json; do
  if [[ ! -s "$rel" ]]; then
    curl -fL --retry 4 --retry-delay 4 -o "$rel" "$BASE/$rel"
  fi
done

echo "laya bundle $DEST/model.onnx"

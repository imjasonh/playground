#!/usr/bin/env bash
# Seeds the corpus and fuzzes each target for FUZZ_SECONDS seconds (default
# 30), with cargo-fuzz and the nightly toolchain in FUZZ_TOOLCHAIN (default
# nightly-2026-11-09). Fails if any target finds an input that panics or
# trips a sanitizer.
#
# Usage: fuzz/run.sh [TARGET...]

set -euo pipefail

fuzz="$(cd "$(dirname "$0")" && pwd)"
seconds="${FUZZ_SECONDS:-30}"
targets=("$@")
if ((${#targets[@]} == 0)); then
  targets=(formats trust sigstore slot)
fi

bash "${fuzz}/seed.sh"
cd "${fuzz}"
for t in "${targets[@]}"; do
  max_len=8192
  if [[ "${t}" == slot ]]; then
    max_len=262144
  fi
  echo "--- fuzzing ${t} for ${seconds}s"
  cargo "+${FUZZ_TOOLCHAIN:-nightly-2026-11-09}" fuzz run "${t}" "corpus/${t}" -- \
    -max_total_time="${seconds}" -max_len="${max_len}" -print_final_stats=1
done

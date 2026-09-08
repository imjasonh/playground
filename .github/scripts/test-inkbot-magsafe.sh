#!/usr/bin/env bash
# Run the complete inkbot-magsafe gate inside the required Test workflow.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
app_dir="${repo_root}/inkbot-magsafe"

cd "$app_dir"
cargo fmt --all --check
cargo clippy --all-targets --locked -- -D warnings
cargo test --locked
python3 -m unittest tools/test_check_elf_layout.py

classification=$(
  python3 -c \
    'import json; print(json.load(open("production-gates.json"))["classification"])'
)
feature_args=()
if [ "$classification" = "PRODUCTION" ]; then
  cargo check --locked --no-default-features \
    --target thumbv7em-none-eabihf
else
  if cargo check --locked --no-default-features \
    --target thumbv7em-none-eabihf; then
    echo "EVT target build succeeded without the explicit inert-image feature"
    exit 1
  fi
  feature_args=(--features bringup-stub)
fi

cargo clippy --locked --no-default-features \
  --target thumbv7em-none-eabihf \
  "${feature_args[@]}" \
  -- -D warnings
cargo build --locked --release --no-default-features \
  --target thumbv7em-none-eabihf \
  "${feature_args[@]}"
elf="${CARGO_TARGET_DIR:-target}/thumbv7em-none-eabihf/release/inkbot-magsafe"
python3 tools/check_elf_layout.py \
  "$elf" \
  --flash-start 0x1c000 \
  --flash-end 0x5c000 \
  --ram-start 0x20008000 \
  --ram-end 0x20040000

cd "$app_dir/kicad"
python3 generate_schematic.py
kicad-cli sch export netlist \
  -o /tmp/inkbot.net \
  inkbot-magsafe.kicad_sch
git diff --exit-code -- \
  inkbot-magsafe.kicad_sch \
  inkbot-magsafe.kicad_pro
INKBOT_PLACE_ONLY=1 python3 route_freerouting.py
python3 release_gates.py
python3 -m unittest test_release_gates.py test_run_drc.py
python3 run_erc.py
python3 run_drc.py

kicad_image="kicad/kicad:9.0@sha256:e638b79b0321f29395a5b783e94bb9f3c73303e8da15da27b8f5cb4b67a37729"
docker run --rm --user root \
  --volume "${repo_root}:/workspace" \
  --workdir /workspace/inkbot-magsafe/kicad \
  "$kicad_image" \
  sh -euc '
    kicad-cli sch erc \
      --format report \
      --severity-error \
      --exit-code-violations \
      --output /tmp/inkbot-erc.rpt \
      inkbot-magsafe.kicad_sch
    cat /tmp/inkbot-erc.rpt
    kicad-cli pcb drc \
      --format report \
      --severity-error \
      --schematic-parity \
      --exit-code-violations \
      --output /tmp/inkbot-drc.rpt \
      inkbot-magsafe.kicad_pcb
    cat /tmp/inkbot-drc.rpt
  '

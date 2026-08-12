#!/usr/bin/env bash
# Benchmark pasta against the playground monorepo with .pasta rules.
# Usage (from repo root):
#   PASTA_BIN=/path/to/pasta ./pasta/scripts/bench-monorepo.sh [label]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LABEL="${1:-run}"
BIN="${PASTA_BIN:-pasta}"
OUT_DIR="${BENCH_OUT:-$ROOT/pasta/bench/results}"
mkdir -p "$OUT_DIR"

if [[ ! -d "$ROOT/.pasta" ]]; then
  echo "error: .pasta/ rules directory required at repo root" >&2
  exit 1
fi

export ROOT
python3 - "$LABEL" "$BIN" "$OUT_DIR" "$ROOT" <<'PY'
import json, os, re, subprocess, sys, time

label, binary, out_dir, root = sys.argv[1:5]
results = []

def run(name, args, repeats=3):
    rows = []
    for i in range(1, repeats + 1):
        t0 = time.perf_counter()
        p = subprocess.run(args, cwd=root, capture_output=True, text=True)
        wall = time.perf_counter() - t0
        stats = {}
        m = re.search(r"^stats: (.+)$", p.stderr, re.M)
        if not m:
            raise SystemExit(f"no stats for {name}#{i}: {p.stderr[-400:]}")
        for part in m.group(1).split():
            if "=" in part:
                k, v = part.split("=", 1)
                try:
                    stats[k] = int(v)
                except ValueError:
                    stats[k] = v
        rows.append({
            "label": name,
            "run": i,
            "wall_sec": round(wall, 3),
            "exit": p.returncode,
            "stats": stats,
            "parse_error_skips": len(re.findall(r"skipped \(parse errors\)", p.stderr)),
            "too_complex_skips": len(re.findall(r"skipped \(too complex", p.stderr)),
            "findings": len(re.findall(r"^\S+:\d+:", p.stderr, re.M)),
        })
        print(json.dumps(rows[-1]), flush=True)
    return rows

base = [binary, "-rules", ".pasta", "-stats", "-fail-on", "none", "./..."]
results += run(f"{label}-cold", [binary, "-nocache", *base[1:]], 3)
run(f"{label}-warm-prime", base, 1)
results += run(f"{label}-warm", base, 3)
path = os.path.join(out_dir, f"{label}.json")
with open(path, "w") as f:
    json.dump({"label": label, "binary": binary, "results": results}, f, indent=2)
print(f"wrote {path}", file=sys.stderr)
PY

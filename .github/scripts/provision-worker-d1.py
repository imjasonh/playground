#!/usr/bin/env python3
"""Apply remote D1 migrations for databases declared in wrangler.toml.

The D1 analog of provision-worker-kv.py / provision-worker-r2.py, run from the
Worker app directory (wrangler-action sets its workingDirectory) before
`wrangler deploy`. Wrangler deploy does not apply D1 migrations on its own.
This is idempotent: already-applied migrations are a no-op.

Requires `wrangler` on PATH (wrangler-action installs it before preCommands).

Environment:
  CLOUDFLARE_API_TOKEN, CLOUDFLARE_ACCOUNT_ID  (wrangler-action provides both)
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tomllib

CONFIG = "wrangler.toml"


def die(msg: str) -> None:
    print(f"provision-worker-d1: {msg}", file=sys.stderr)
    sys.exit(1)


def wrangler_argv() -> list[str]:
    """Prefer the wrangler wrangler-action put on PATH, then a local install."""
    found = shutil.which("wrangler")
    if found:
        return [found]
    local = os.path.join("node_modules", ".bin", "wrangler")
    if os.path.isfile(local):
        return [local]
    die("wrangler not found on PATH or in ./node_modules/.bin")
    return []  # unreachable; keeps type-checkers happy


def main() -> int:
    if not os.path.isfile(CONFIG):
        print(f"No {CONFIG} in {os.getcwd()}; nothing to provision.")
        return 0

    with open(CONFIG, "rb") as fh:
        cfg = tomllib.load(fh)

    databases = cfg.get("d1_databases", [])
    if not databases:
        print("No [[d1_databases]] entries; nothing to migrate.")
        return 0

    if not os.environ.get("CLOUDFLARE_API_TOKEN"):
        die("CLOUDFLARE_API_TOKEN must be set")
    if not os.environ.get("CLOUDFLARE_ACCOUNT_ID"):
        die("CLOUDFLARE_ACCOUNT_ID must be set")

    wrangler = wrangler_argv()
    for db in databases:
        name = db.get("database_name")
        if not name:
            die("a [[d1_databases]] entry is missing `database_name`")
        cmd = wrangler + ["d1", "migrations", "apply", name, "--remote"]
        print(f"Applying D1 migrations for '{name}': {' '.join(cmd)}")
        result = subprocess.run(cmd, check=False)
        if result.returncode != 0:
            die(f"wrangler d1 migrations apply {name} --remote failed ({result.returncode})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Require Workers Logs and Traces in every Worker app's wrangler.toml.

Playground Cloudflare Worker apps persist invocation logs and automatic
traces by default (see AGENTS.md). `[observability] enabled` turns on
Workers Logs; traces still need their own `[observability.traces]` block.
Invocation logs (request/response/`outcome` metadata) stay on unless a
Worker explicitly sets `invocation_logs = false`.

Usage:
  check-worker-observability.py --all
  check-worker-observability.py path/to/wrangler.toml [...]
"""

from __future__ import annotations

import argparse
import sys
import tomllib
from pathlib import Path


def die(msg: str) -> None:
    print(f"check-worker-observability: {msg}", file=sys.stderr)
    sys.exit(1)


def discover_worker_configs(root: Path) -> list[Path]:
    """Top-level non-hidden directories that contain wrangler.toml."""
    configs: list[Path] = []
    for child in sorted(root.iterdir()):
        if not child.is_dir() or child.name.startswith("."):
            continue
        config = child / "wrangler.toml"
        if config.is_file():
            configs.append(config)
    return configs


def check_config(path: Path) -> list[str]:
    try:
        data = tomllib.loads(path.read_text())
    except (OSError, tomllib.TOMLDecodeError) as err:
        return [f"{path}: cannot parse wrangler.toml: {err}"]

    obs = data.get("observability")
    if not isinstance(obs, dict):
        return [
            f"{path}: missing [observability] (enable Workers Logs and Traces)"
        ]

    errors: list[str] = []
    if obs.get("enabled") is not True:
        errors.append(f"{path}: [observability] enabled = true is required")

    logs = obs.get("logs")
    if logs is None:
        logs = {}
    if not isinstance(logs, dict):
        errors.append(f"{path}: [observability.logs] must be a table")
    else:
        if logs.get("enabled") is False:
            errors.append(f"{path}: [observability.logs] enabled = true is required")
        if logs.get("invocation_logs") is False:
            errors.append(
                f"{path}: [observability.logs] invocation_logs must stay enabled"
            )

    traces = obs.get("traces")
    if not isinstance(traces, dict):
        errors.append(
            f"{path}: missing [observability.traces] enabled = true"
        )
    elif traces.get("enabled") is not True:
        errors.append(f"{path}: [observability.traces] enabled = true is required")

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--all",
        action="store_true",
        help="check every top-level Worker app in this repo",
    )
    parser.add_argument(
        "configs",
        nargs="*",
        type=Path,
        help="wrangler.toml paths to check",
    )
    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[2]
    paths: list[Path] = []
    if args.all:
        paths.extend(discover_worker_configs(repo_root))
    paths.extend(args.configs)

    if not paths:
        die("pass --all or one or more wrangler.toml paths")

    errors: list[str] = []
    for path in paths:
        errors.extend(check_config(path))

    if errors:
        for err in errors:
            print(f"check-worker-observability: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

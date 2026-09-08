#!/usr/bin/env python3
"""Validate evidence-backed hardware release gates."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_PATH = HERE.parent / "production-gates.json"
VALID_CLASSIFICATIONS = {"EVT", "DVT", "PVT", "PRODUCTION"}
VALID_STATUSES = {"blocked", "passed"}


@dataclass(frozen=True)
class GateSummary:
    classification: str
    passed: tuple[str, ...]
    blocked: tuple[str, ...]
    evidence_files: tuple[Path, ...]

    @property
    def production_releasable(self) -> bool:
        return self.classification == "PRODUCTION" and not self.blocked


def validate_release_gates(path: Path = DEFAULT_PATH) -> GateSummary:
    """Load and validate a release-gate file."""
    data = json.loads(path.read_text())
    evidence_root = path.resolve().parent
    if data.get("schema_version") != 1:
        raise ValueError("schema_version must be 1")
    if data.get("product") != "inkbot-magsafe":
        raise ValueError("product must be inkbot-magsafe")
    classification = data.get("classification")
    if classification not in VALID_CLASSIFICATIONS:
        raise ValueError(f"invalid classification: {classification!r}")
    gates = data.get("gates")
    if not isinstance(gates, list) or not gates:
        raise ValueError("gates must be a nonempty list")

    seen: set[str] = set()
    passed: list[str] = []
    blocked: list[str] = []
    evidence_files: set[Path] = set()
    for index, gate in enumerate(gates):
        if not isinstance(gate, dict):
            raise ValueError(f"gate {index} must be an object")
        gate_id = gate.get("id")
        if not isinstance(gate_id, str) or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", gate_id):
            raise ValueError(f"gate {index} has an invalid id")
        if gate_id in seen:
            raise ValueError(f"duplicate gate id: {gate_id}")
        seen.add(gate_id)

        status = gate.get("status")
        if status not in VALID_STATUSES:
            raise ValueError(f"gate {gate_id} has invalid status: {status!r}")
        evidence = gate.get("evidence")
        if not isinstance(evidence, list) or not all(
            isinstance(item, str) and item.strip() for item in evidence
        ):
            raise ValueError(f"gate {gate_id} evidence must contain nonempty strings")
        if len(evidence) != len(set(evidence)):
            raise ValueError(f"gate {gate_id} contains duplicate evidence paths")
        for item in evidence:
            candidate = Path(item)
            if candidate.is_absolute():
                raise ValueError(f"gate {gate_id} evidence path must be relative: {item}")
            resolved = (evidence_root / candidate).resolve()
            try:
                resolved.relative_to(evidence_root)
            except ValueError as error:
                raise ValueError(
                    f"gate {gate_id} evidence path escapes the release directory: {item}"
                ) from error
            if not resolved.is_file():
                raise ValueError(f"gate {gate_id} evidence file does not exist: {item}")
            evidence_files.add(resolved)
        if status == "passed" and not evidence:
            raise ValueError(f"passed gate {gate_id} requires evidence")
        (passed if status == "passed" else blocked).append(gate_id)

    if classification == "PRODUCTION" and blocked:
        raise ValueError("PRODUCTION classification cannot contain blocked gates")
    return GateSummary(
        classification,
        tuple(passed),
        tuple(blocked),
        tuple(sorted(evidence_files)),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", type=Path, default=DEFAULT_PATH)
    parser.add_argument(
        "--production",
        action="store_true",
        help="fail unless every gate has evidence and the classification is PRODUCTION",
    )
    args = parser.parse_args()

    try:
        summary = validate_release_gates(args.path)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}")
        return 1

    print(
        f"release gates: {summary.classification}, "
        f"{len(summary.passed)} passed, {len(summary.blocked)} blocked"
    )
    for gate_id in summary.blocked:
        print(f"  blocked: {gate_id}")
    if args.production and not summary.production_releasable:
        print("ERROR: production release requested before every gate passed")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

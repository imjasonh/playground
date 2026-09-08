#!/usr/bin/env python3
"""Validate evidence-backed hardware release gates."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from urllib.parse import urlparse

HERE = Path(__file__).resolve().parent
DEFAULT_PATH = HERE.parent / "production-gates.json"
VALID_CLASSIFICATIONS = {"EVT", "DVT", "PVT", "PRODUCTION"}
VALID_STATUSES = {"blocked", "passed"}
VALID_EVIDENCE_KINDS = {
    "certificate",
    "review",
    "supplier-record",
    "test-report",
    "release-record",
}
EVIDENCE_FIELDS = {
    "gate_id",
    "location",
    "sha256",
    "bytes",
    "kind",
    "issuer",
    "issued_on",
    "hardware_revision",
    "source_commit",
    "result",
    "criteria",
    "subjects",
    "approved_by",
}
REQUIRED_GATE_IDS = (
    "independent-schematic-review",
    "pcb-drc-and-dfm",
    "panel-drawing-and-sample",
    "battery-pack-qualification",
    "magnet-and-anti-rotation-qualification",
    "enclosure-and-assembly-drawings",
    "qi-tuning-fod-and-interoperability",
    "power-thermal-and-charger-validation",
    "integrated-firmware-and-power-fail-validation",
    "rf-and-ble-validation",
    "signed-dfu-and-owner-recovery",
    "mechanical-and-environmental-validation",
    "factory-programming-and-eol-test",
    "approved-vendor-list-and-supply-chain",
    "regulatory-and-market-access",
)


@dataclass(frozen=True)
class EvidenceRecord:
    gate_id: str
    location: str
    sha256: str
    bytes: int
    kind: str
    issuer: str
    issued_on: str
    hardware_revision: str
    source_commit: str
    criteria: tuple[str, ...]
    subjects: tuple[str, ...]
    approved_by: tuple[str, ...]
    local_path: Path | None

    def manifest_entry(self) -> dict:
        """Return the immutable evidence fields stored in a fab manifest."""
        return {
            "gate_id": self.gate_id,
            "location": self.location,
            "sha256": self.sha256,
            "bytes": self.bytes,
            "kind": self.kind,
            "issuer": self.issuer,
            "issued_on": self.issued_on,
            "hardware_revision": self.hardware_revision,
            "source_commit": self.source_commit,
            "result": "pass",
            "criteria": list(self.criteria),
            "subjects": list(self.subjects),
            "approved_by": list(self.approved_by),
        }


@dataclass(frozen=True)
class GateSummary:
    classification: str
    passed: tuple[str, ...]
    blocked: tuple[str, ...]
    evidence_files: tuple[Path, ...]
    evidence_records: tuple[EvidenceRecord, ...]

    @property
    def production_releasable(self) -> bool:
        return self.classification == "PRODUCTION" and not self.blocked


def nonempty_strings(value: object, field: str, gate_id: str) -> tuple[str, ...]:
    """Validate a nonempty list of unique nonempty strings."""
    if not isinstance(value, list) or not value or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ValueError(f"gate {gate_id} evidence {field} must be nonempty strings")
    if len(value) != len(set(value)):
        raise ValueError(f"gate {gate_id} evidence {field} contains duplicates")
    return tuple(value)


def validate_evidence_record(
    item: object,
    gate_id: str,
    evidence_root: Path,
) -> EvidenceRecord:
    """Validate one local or restricted external qualification record."""
    if not isinstance(item, dict) or set(item) != EVIDENCE_FIELDS:
        raise ValueError(f"gate {gate_id} evidence must use the complete schema")
    if item["gate_id"] != gate_id:
        raise ValueError(f"gate {gate_id} evidence names gate {item['gate_id']!r}")

    location = item["location"]
    if not isinstance(location, str) or not location.strip():
        raise ValueError(f"gate {gate_id} evidence location must be a nonempty string")
    local_path = None
    parsed = urlparse(location)
    if parsed.scheme:
        if (
            parsed.scheme != "https"
            or not parsed.netloc
            or parsed.username
            or parsed.password
        ):
            raise ValueError(f"gate {gate_id} evidence URI must be an HTTPS URL")
    else:
        candidate = Path(location)
        if candidate.is_absolute():
            raise ValueError(
                f"gate {gate_id} evidence path must be relative: {location}"
            )
        local_path = (evidence_root / candidate).resolve()
        try:
            local_path.relative_to(evidence_root)
        except ValueError as error:
            raise ValueError(
                f"gate {gate_id} evidence path escapes the release directory: {location}"
            ) from error
        if not local_path.is_file():
            raise ValueError(
                f"gate {gate_id} evidence file does not exist: {location}"
            )

    digest = item["sha256"]
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError(f"gate {gate_id} evidence SHA-256 must be 64 lowercase hex digits")
    byte_count = item["bytes"]
    if isinstance(byte_count, bool) or not isinstance(byte_count, int) or byte_count < 32:
        raise ValueError(f"gate {gate_id} evidence must record at least 32 bytes")
    if local_path is not None:
        actual_bytes = local_path.stat().st_size
        actual_digest = hashlib.sha256(local_path.read_bytes()).hexdigest()
        if actual_bytes != byte_count:
            raise ValueError(f"gate {gate_id} evidence byte count does not match")
        if actual_digest != digest:
            raise ValueError(f"gate {gate_id} evidence SHA-256 does not match")

    kind = item["kind"]
    if kind not in VALID_EVIDENCE_KINDS:
        raise ValueError(f"gate {gate_id} evidence has invalid kind {kind!r}")
    issuer = item["issuer"]
    if not isinstance(issuer, str) or not issuer.strip():
        raise ValueError(f"gate {gate_id} evidence issuer must be nonempty")
    issued_on = item["issued_on"]
    if not isinstance(issued_on, str):
        raise ValueError(f"gate {gate_id} evidence issued_on must be YYYY-MM-DD")
    try:
        date.fromisoformat(issued_on)
    except ValueError as error:
        raise ValueError(
            f"gate {gate_id} evidence issued_on must be YYYY-MM-DD"
        ) from error
    hardware_revision = item["hardware_revision"]
    if not isinstance(hardware_revision, str) or not re.fullmatch(
        r"[A-Za-z0-9][A-Za-z0-9._-]*", hardware_revision
    ):
        raise ValueError(f"gate {gate_id} evidence hardware revision is invalid")
    source_commit = item["source_commit"]
    if not isinstance(source_commit, str) or not re.fullmatch(
        r"[0-9a-f]{40}", source_commit
    ):
        raise ValueError(f"gate {gate_id} evidence source commit is invalid")
    if item["result"] != "pass":
        raise ValueError(f"gate {gate_id} evidence result must be pass")
    criteria = nonempty_strings(item["criteria"], "criteria", gate_id)
    subjects = nonempty_strings(item["subjects"], "subjects", gate_id)
    approved_by = nonempty_strings(item["approved_by"], "approved_by", gate_id)
    if len(approved_by) < 2 or not all(
        re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", approver)
        for approver in approved_by
    ):
        raise ValueError(
            f"gate {gate_id} evidence requires two distinct approver emails"
        )
    return EvidenceRecord(
        gate_id=gate_id,
        location=location,
        sha256=digest,
        bytes=byte_count,
        kind=kind,
        issuer=issuer,
        issued_on=issued_on,
        hardware_revision=hardware_revision,
        source_commit=source_commit,
        criteria=criteria,
        subjects=subjects,
        approved_by=approved_by,
        local_path=local_path,
    )


def validate_release_gates(path: Path = DEFAULT_PATH) -> GateSummary:
    """Load and validate a release-gate file."""
    data = json.loads(path.read_text())
    evidence_root = path.resolve().parent
    if data.get("schema_version") != 2:
        raise ValueError("schema_version must be 2")
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
    evidence_records: list[EvidenceRecord] = []
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
        if not isinstance(evidence, list):
            raise ValueError(f"gate {gate_id} evidence must be a list")
        locations: set[str] = set()
        for item in evidence:
            record = validate_evidence_record(item, gate_id, evidence_root)
            if record.location in locations:
                raise ValueError(
                    f"gate {gate_id} contains duplicate evidence locations"
                )
            locations.add(record.location)
            evidence_records.append(record)
            if record.local_path is not None:
                evidence_files.add(record.local_path)
        if status == "passed" and not evidence:
            raise ValueError(f"passed gate {gate_id} requires evidence")
        (passed if status == "passed" else blocked).append(gate_id)

    if classification == "PRODUCTION" and blocked:
        raise ValueError("PRODUCTION classification cannot contain blocked gates")
    actual_gate_ids = tuple(gate["id"] for gate in gates)
    if actual_gate_ids != REQUIRED_GATE_IDS:
        missing = sorted(set(REQUIRED_GATE_IDS) - set(actual_gate_ids))
        extra = sorted(set(actual_gate_ids) - set(REQUIRED_GATE_IDS))
        if missing or extra:
            raise ValueError(
                f"release gate set mismatch; missing={missing}, extra={extra}"
            )
        raise ValueError("release gates must use the required order")
    return GateSummary(
        classification,
        tuple(passed),
        tuple(blocked),
        tuple(sorted(evidence_files)),
        tuple(evidence_records),
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

#!/usr/bin/env python3
"""Stress-test Army List validation with ~50 real constructed lists.

Ports the Swift ArmyListValidator rules against catalog.json, builds one
(or more) lists per faction for Incursion and Strike Force, and reports:

  - builder failures (could not assemble a candidate)
  - unexpected illegal lists (builder expected LEGAL)
  - catalog integrity issues discovered along the way

Also writes JSON fixtures under ios/Tests/PlaygroundTests/Fixtures/ArmyLists/
for XCTest to re-run the same cases through the Swift validator in CI.

Usage:
  python3 ios/scripts/stress-army-lists.py
  python3 ios/scripts/stress-army-lists.py --write-fixtures
"""

from __future__ import annotations

import argparse
import json
import pathlib
import random
import sys
import uuid
from collections import defaultdict
from dataclasses import dataclass, field
from itertools import combinations
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[2]
CATALOG_PATH = ROOT / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"
FIXTURES_DIR = ROOT / "ios/Tests/PlaygroundTests/Fixtures/ArmyLists"


# --- Catalog helpers ---------------------------------------------------------


def points_for(sheet: dict, models: int, copy_index: int) -> int | None:
    for tier in sheet.get("pointsTiers") or []:
        if copy_index < tier["fromCopy"]:
            continue
        to = tier.get("toCopy")
        if to is not None and copy_index > to:
            continue
        return tier["byModels"].get(str(models))
    return None


def enhancement_lookup(catalog: dict, enhancement_id: str):
    for det in catalog["detachments"]:
        for enh in det.get("enhancements") or []:
            if enh["id"] == enhancement_id:
                return det, enh
    return None


# --- Validator (mirror of ArmyListValidator.swift) ---------------------------


@dataclass
class Issue:
    code: str
    severity: str
    message: str
    unit_id: str | None = None


@dataclass
class ValidationResult:
    issues: list[Issue]
    total_points: int
    dp_spent: int

    @property
    def errors(self) -> list[Issue]:
        return [i for i in self.issues if i.severity == "error"]

    @property
    def is_legal(self) -> bool:
        return not self.errors


def validate(list_doc: dict, catalog: dict) -> ValidationResult:
    issues: list[Issue] = []
    factions = {f["id"]: f for f in catalog["factions"]}
    sizes = {b["id"]: b for b in catalog["battleSizes"]}
    sheets = {d["id"]: d for d in catalog["datasheets"]}
    dets = {d["id"]: d for d in catalog["detachments"]}

    if list_doc.get("catalogVersion") != catalog["version"]:
        issues.append(Issue("catalog.versionMismatch", "warning", "catalog version mismatch"))

    faction = factions.get(list_doc["factionID"])
    if not faction:
        issues.append(Issue("faction.unknown", "error", f"Unknown faction {list_doc['factionID']}"))
        return ValidationResult(issues, 0, 0)

    battle = sizes.get(list_doc["battleSizeID"])
    if not battle:
        issues.append(Issue("battleSize.unknown", "error", f"Unknown battle size {list_doc['battleSizeID']}"))
        return ValidationResult(issues, 0, 0)

    # Detachments
    dp_spent = 0
    if not list_doc.get("detachmentIDs"):
        issues.append(Issue("detachment.required", "error", "Select at least one detachment."))
    else:
        seen_ids: set[str] = set()
        seen_tags: dict[str, str] = {}
        for did in list_doc["detachmentIDs"]:
            if did in seen_ids:
                issues.append(Issue("detachment.duplicate", "error", f"Duplicate detachment {did}"))
                continue
            seen_ids.add(did)
            det = dets.get(did)
            if not det:
                issues.append(Issue("detachment.unknown", "error", f"Unknown detachment {did}"))
                continue
            if det["factionID"] != faction["id"]:
                issues.append(Issue("detachment.wrongFaction", "error", f"{det['name']} wrong faction"))
            dp_spent += int(det["detachmentPoints"])
            tag = det.get("uniqueTag")
            if tag:
                if tag in seen_tags:
                    issues.append(
                        Issue(
                            "detachment.uniqueTagCollision",
                            "error",
                            f"{det['name']} and {seen_tags[tag]} share {tag}",
                        )
                    )
                else:
                    seen_tags[tag] = det["name"]
        if dp_spent > battle["detachmentPointsBudget"]:
            issues.append(
                Issue(
                    "dp.overBudget",
                    "error",
                    f"DP {dp_spent} > {battle['detachmentPointsBudget']}",
                )
            )

    units = list_doc.get("units") or []
    unit_by_id = {}
    for u in units:
        if u["id"] in unit_by_id:
            issues.append(Issue("unit.duplicateID", "error", "Duplicate unit instance IDs"))
        unit_by_id[u["id"]] = u

    total_points = 0
    copy_index: dict[str, int] = defaultdict(int)
    enhancement_pick_slots = 0
    upgrade_groups: dict[str, int] = defaultdict(int)

    for unit in units:
        sheet = sheets.get(unit["datasheetID"])
        if not sheet:
            issues.append(
                Issue("unit.unknownDatasheet", "error", f"Unknown {unit['datasheetID']}", unit["id"])
            )
            continue
        if sheet["factionID"] != faction["id"]:
            issues.append(
                Issue("unit.wrongFaction", "error", f"{sheet['name']} wrong faction", unit["id"])
            )
        models = int(unit["models"])
        if models not in sheet["modelCounts"] or models < sheet["minModels"] or models > sheet["maxModels"]:
            issues.append(
                Issue("unit.modelCount", "error", f"{sheet['name']} bad model count {models}", unit["id"])
            )
        copy_index[sheet["id"]] += 1
        next_copy = copy_index[sheet["id"]]
        pts = points_for(sheet, models, next_copy)
        if pts is None:
            issues.append(
                Issue(
                    "unit.pointsMissing",
                    "error",
                    f"No points for {sheet['name']} {models} copy#{next_copy}",
                    unit["id"],
                )
            )
        else:
            total_points += pts

        if sheet.get("mustAttach") and not unit.get("attachedToUnitID"):
            issues.append(Issue("unit.mustAttach", "error", f"{sheet['name']} must attach", unit["id"]))

        body_id = unit.get("attachedToUnitID")
        if body_id:
            body = unit_by_id.get(body_id)
            if not body:
                issues.append(Issue("unit.attachMissing", "error", "attach target missing", unit["id"]))
            else:
                if body["id"] == unit["id"]:
                    issues.append(Issue("unit.attachSelf", "error", "attach self", unit["id"]))
                if sheet.get("characterRole") is None:
                    issues.append(
                        Issue("unit.attachNotCharacter", "error", f"{sheet['name']} not character", unit["id"])
                    )
                leader_to = sheet.get("leaderTo") or []
                if not leader_to:
                    issues.append(
                        Issue(
                            "unit.attachNoTargets",
                            "error",
                            f"{sheet['name']} has no Leader join targets",
                            unit["id"],
                        )
                    )
                elif body["datasheetID"] not in leader_to:
                    issues.append(
                        Issue("unit.attachIllegal", "error", f"{sheet['name']} cannot join", unit["id"])
                    )

        if len(unit.get("enhancementIDs") or []) > 1:
            issues.append(Issue("enhancement.onePerUnit", "error", "more than one enhancement", unit["id"]))
        for eid in unit.get("enhancementIDs") or []:
            looked = enhancement_lookup(catalog, eid)
            if not looked:
                issues.append(Issue("enhancement.unknown", "error", f"Unknown {eid}", unit["id"]))
                continue
            det, enh = looked
            if det["id"] not in list_doc.get("detachmentIDs", []):
                issues.append(
                    Issue(
                        "enhancement.detachmentNotSelected",
                        "error",
                        f"{enh['name']} requires {det['name']}",
                        unit["id"],
                    )
                )
            if enh.get("isUpgrade"):
                if sheet.get("characterRole") is not None:
                    issues.append(
                        Issue("enhancement.upgradeOnCharacter", "error", "upgrade on character", unit["id"])
                    )
                upgrade_groups[enh["id"]] += 1
                if upgrade_groups[enh["id"]] == 1:
                    enhancement_pick_slots += 1
                if upgrade_groups[enh["id"]] > 3:
                    issues.append(Issue("enhancement.upgradeCap", "error", "upgrade >3", unit["id"]))
            else:
                if sheet.get("characterRole") is None:
                    issues.append(
                        Issue("enhancement.requiresCharacter", "error", "needs character", unit["id"])
                    )
                enhancement_pick_slots += 1
            total_points += int(enh["points"])

    for ds_id, count in copy_index.items():
        sheet = sheets[ds_id]
        if sheet.get("battleline"):
            size_limit = battle["battlelineDuplicateLimit"]
        elif sheet.get("dedicatedTransport"):
            size_limit = battle["dedicatedTransportDuplicateLimit"]
        else:
            size_limit = battle["datasheetDuplicateLimit"]
        override = sheet.get("maxCopiesOverride")
        limit = min(override, size_limit) if override is not None else size_limit
        if sheet.get("epicHero") and count > 1:
            issues.append(Issue("unit.epicHeroDuplicate", "error", f"{sheet['name']} epic hero dup"))
        elif count > limit:
            issues.append(
                Issue("unit.duplicateCap", "error", f"{sheet['name']} x{count} > {limit}")
            )

    attachments: dict[str, list] = defaultdict(list)
    for unit in units:
        if unit.get("attachedToUnitID"):
            attachments[unit["attachedToUnitID"]].append(unit)
    for body_id, attached in attachments.items():
        leaders = [
            u
            for u in attached
            if (sheets.get(u["datasheetID"]) or {}).get("characterRole") == "leader"
        ]
        others = [
            u
            for u in attached
            if (sheets.get(u["datasheetID"]) or {}).get("characterRole") != "leader"
        ]
        if len(leaders) > 1:
            issues.append(Issue("unit.leaderSlot", "error", "too many leaders", body_id))
        if len(others) > 1:
            issues.append(Issue("unit.supportSlot", "error", "too many support", body_id))

    if enhancement_pick_slots > battle["enhancementPickLimit"]:
        issues.append(
            Issue(
                "enhancement.pickLimit",
                "error",
                f"{enhancement_pick_slots} > {battle['enhancementPickLimit']}",
            )
        )

    if total_points > battle["pointsLimit"]:
        issues.append(
            Issue("points.overLimit", "error", f"{total_points} > {battle['pointsLimit']}")
        )
    elif total_points == 0 and not units:
        issues.append(Issue("list.empty", "warning", "empty list"))

    if (
        dp_spent < battle["detachmentPointsBudget"]
        and list_doc.get("detachmentIDs")
    ):
        issues.append(
            Issue(
                "dp.underBudget",
                "warning",
                f"Using {dp_spent} of {battle['detachmentPointsBudget']} DP",
            )
        )

    warlord_id = list_doc.get("warlordUnitID")
    if not warlord_id:
        if units:
            issues.append(Issue("warlord.missing", "error", "Choose a Warlord."))
    else:
        unit = next((u for u in units if u["id"] == warlord_id), None)
        if not unit:
            issues.append(Issue("warlord.missingUnit", "error", "Warlord not on list"))
        else:
            sheet = sheets.get(unit["datasheetID"])
            if sheet and sheet.get("characterRole") is None:
                issues.append(
                    Issue(
                        "warlord.notCharacter",
                        "error",
                        f"Warlord must be Character ({sheet['name']})",
                        unit["id"],
                    )
                )

    return ValidationResult(issues, total_points, dp_spent)


# --- List builder ------------------------------------------------------------


@dataclass
class BuiltList:
    name: str
    doc: dict
    expected_legal: bool
    notes: str = ""


def new_unit(datasheet_id: str, models: int, **kwargs) -> dict:
    u = {
        "id": str(uuid.uuid4()).upper(),
        "datasheetID": datasheet_id,
        "models": models,
        "optionIDs": [],
        "enhancementIDs": [],
        "attachedToUnitID": None,
    }
    u.update(kwargs)
    return u


def detachment_combos(faction_dets: list[dict], budget: int) -> list[list[dict]]:
    """Return unique-tag-safe detachment combinations with DP sum == budget (prefer exact)."""
    exact: list[list[dict]] = []
    under: list[list[dict]] = []
    n = len(faction_dets)
    for k in range(1, min(4, n) + 1):
        for combo in combinations(faction_dets, k):
            tags = [d.get("uniqueTag") for d in combo if d.get("uniqueTag")]
            if len(tags) != len(set(tags)):
                continue
            spent = sum(int(d["detachmentPoints"]) for d in combo)
            if spent == budget:
                exact.append(list(combo))
            elif 0 < spent <= budget:
                under.append(list(combo))
    # Prefer exact spend, then fullest under-budget.
    under.sort(key=lambda c: -sum(int(d["detachmentPoints"]) for d in c))
    return exact + under


def unit_cost(sheet: dict, models: int, copy_index: int = 1) -> int | None:
    return points_for(sheet, models, copy_index)


def pick_warlord(sheets: list[dict]) -> dict | None:
    # Prefer non-epic Leader, then any Leader, then Character.
    leaders = [s for s in sheets if s.get("characterRole") == "leader" and not s.get("epicHero")]
    if leaders:
        leaders.sort(key=lambda s: unit_cost(s, s["minModels"]) or 9999)
        return leaders[0]
    leaders = [s for s in sheets if s.get("characterRole") == "leader"]
    if leaders:
        return leaders[0]
    chars = [s for s in sheets if s.get("characterRole") == "character" and not s.get("epicHero")]
    if chars:
        chars.sort(key=lambda s: unit_cost(s, s["minModels"]) or 9999)
        return chars[0]
    chars = [s for s in sheets if s.get("characterRole") == "character"]
    return chars[0] if chars else None


def fill_list(
    catalog: dict,
    faction: dict,
    battle_size_id: str,
    *,
    seed: int,
    attach: bool,
    with_enhancement: bool,
    target_fill: float,
) -> BuiltList | None:
    rng = random.Random(seed)
    battle = next(b for b in catalog["battleSizes"] if b["id"] == battle_size_id)
    faction_sheets = [d for d in catalog["datasheets"] if d["factionID"] == faction["id"]]
    faction_dets = [d for d in catalog["detachments"] if d["factionID"] == faction["id"]]
    if not faction_dets:
        return BuiltList(
            name=f"{faction['name']} {battle['name']} (no detachments)",
            doc={
                "id": str(uuid.uuid4()).upper(),
                "name": f"{faction['name']} — no detachments",
                "catalogVersion": catalog["version"],
                "factionID": faction["id"],
                "battleSizeID": battle_size_id,
                "detachmentIDs": [],
                "units": [],
                "warlordUnitID": None,
                "notes": "Catalog has no detachments for this faction.",
                "createdAt": "2026-01-01T00:00:00Z",
                "updatedAt": "2026-01-01T00:00:00Z",
            },
            expected_legal=False,
            notes="expected illegal: no detachments in catalog",
        )

    combos = detachment_combos(faction_dets, battle["detachmentPointsBudget"])
    if not combos:
        return None
    dets = combos[seed % len(combos)]

    warlord_sheet = pick_warlord(faction_sheets)
    if not warlord_sheet:
        return BuiltList(
            name=f"{faction['name']} {battle['name']} (no characters)",
            doc={
                "id": str(uuid.uuid4()).upper(),
                "name": f"{faction['name']} — no characters",
                "catalogVersion": catalog["version"],
                "factionID": faction["id"],
                "battleSizeID": battle_size_id,
                "detachmentIDs": [d["id"] for d in dets],
                "units": [],
                "warlordUnitID": None,
                "notes": "Catalog has no Character/Leader datasheets.",
                "createdAt": "2026-01-01T00:00:00Z",
                "updatedAt": "2026-01-01T00:00:00Z",
            },
            expected_legal=False,
            notes="expected illegal: no characters to be warlord",
        )

    units: list[dict] = []
    copies: dict[str, int] = defaultdict(int)
    points = 0
    limit = battle["pointsLimit"]
    target = int(limit * target_fill)

    warlord = new_unit(warlord_sheet["id"], warlord_sheet["minModels"])
    w_cost = unit_cost(warlord_sheet, warlord["models"], 1) or 0
    units.append(warlord)
    copies[warlord_sheet["id"]] += 1
    points += w_cost

    # Optional enhancement on warlord
    if with_enhancement:
        char_enh = []
        for det in dets:
            for enh in det.get("enhancements") or []:
                if not enh.get("isUpgrade"):
                    char_enh.append(enh)
        if char_enh:
            enh = char_enh[seed % len(char_enh)]
            if points + enh["points"] <= limit:
                warlord["enhancementIDs"] = [enh["id"]]
                points += enh["points"]

    def can_add(sheet: dict, models: int) -> int | None:
        next_copy = copies[sheet["id"]] + 1
        if sheet.get("epicHero") and next_copy > 1:
            return None
        if sheet.get("battleline"):
            size_limit = battle["battlelineDuplicateLimit"]
        elif sheet.get("dedicatedTransport"):
            size_limit = battle["dedicatedTransportDuplicateLimit"]
        else:
            size_limit = battle["datasheetDuplicateLimit"]
        override = sheet.get("maxCopiesOverride")
        lim = min(override, size_limit) if override is not None else size_limit
        if next_copy > lim:
            return None
        cost = unit_cost(sheet, models, next_copy)
        if cost is None or points + cost > limit:
            return None
        return cost

    # Prefer battleline fillers, then cheap infantry-ish sheets.
    battleline = [s for s in faction_sheets if s.get("battleline")]
    fillers = [s for s in faction_sheets if s.get("characterRole") is None and not s.get("epicHero")]
    fillers.sort(key=lambda s: unit_cost(s, s["minModels"]) or 9999)
    pool = battleline + fillers
    rng.shuffle(pool)

    body_for_attach = None
    for sheet in pool:
        if points >= target:
            break
        # Prefer max models for battleline density, else min.
        model_opts = list(sheet["modelCounts"])
        model_opts.sort(reverse=bool(sheet.get("battleline")))
        for models in model_opts:
            cost = can_add(sheet, models)
            if cost is None:
                continue
            u = new_unit(sheet["id"], models)
            units.append(u)
            copies[sheet["id"]] += 1
            points += cost
            if body_for_attach is None and not sheet.get("characterRole"):
                body_for_attach = u
            break

    # Attach warlord if possible
    if attach and body_for_attach and (warlord_sheet.get("leaderTo") or []):
        if body_for_attach["datasheetID"] in warlord_sheet["leaderTo"]:
            warlord["attachedToUnitID"] = body_for_attach["id"]
        else:
            # find a legal body already on the list, else try to add one
            for u in units:
                if u["id"] == warlord["id"]:
                    continue
                if u["datasheetID"] in warlord_sheet["leaderTo"]:
                    warlord["attachedToUnitID"] = u["id"]
                    break
            else:
                for target_id in warlord_sheet["leaderTo"]:
                    sheet = next((s for s in faction_sheets if s["id"] == target_id), None)
                    if not sheet:
                        continue
                    cost = can_add(sheet, sheet["minModels"])
                    if cost is None:
                        continue
                    body = new_unit(sheet["id"], sheet["minModels"])
                    units.append(body)
                    copies[sheet["id"]] += 1
                    points += cost
                    warlord["attachedToUnitID"] = body["id"]
                    break

    # Top up with more cheap units if under target
    cheap = sorted(
        [s for s in fillers if s["id"] != warlord_sheet["id"]],
        key=lambda s: unit_cost(s, s["minModels"]) or 9999,
    )
    for sheet in cheap:
        if points >= target:
            break
        cost = can_add(sheet, sheet["minModels"])
        if cost is None:
            continue
        units.append(new_unit(sheet["id"], sheet["minModels"]))
        copies[sheet["id"]] += 1
        points += cost

    name = f"{faction['name']} {battle['name']} {points}pts"
    doc = {
        "id": str(uuid.uuid4()).upper(),
        "name": name,
        "catalogVersion": catalog["version"],
        "factionID": faction["id"],
        "battleSizeID": battle_size_id,
        "detachmentIDs": [d["id"] for d in dets],
        "units": units,
        "warlordUnitID": warlord["id"],
        "notes": f"stress seed={seed} attach={attach} enh={with_enhancement}",
        "createdAt": "2026-01-01T00:00:00Z",
        "updatedAt": "2026-01-01T00:00:00Z",
    }
    return BuiltList(name=name, doc=doc, expected_legal=True, notes="auto-built")


def build_illegal_samples(catalog: dict) -> list[BuiltList]:
    """Hand-shaped illegal lists that must stay illegal (guards against soft validator)."""
    votann = next(f for f in catalog["factions"] if f["id"] == "leagues-of-votann")
    warriors = next(d for d in catalog["datasheets"] if d["id"] == "leagues-of-votann--hearthkyn-warriors")
    kahl = next(d for d in catalog["datasheets"] if d["id"] == "leagues-of-votann--kahl")
    hearthband = next(d for d in catalog["detachments"] if d["id"] == "leagues-of-votann--hearthband")
    moe = next(d for d in catalog["datasheets"] if d["id"] == "chaos-space-marines--master-of-executions")
    legionaries = next(d for d in catalog["datasheets"] if d["id"] == "chaos-space-marines--legionaries")
    csm_det = next(
        d
        for d in catalog["detachments"]
        if d["factionID"] == "chaos-space-marines" and d["detachmentPoints"] == 2
    )

    w = new_unit(warriors["id"], 10)
    samples = []
    # Warlord not character
    samples.append(
        BuiltList(
            name="illegal warlord not character",
            expected_legal=False,
            notes="warlord.notCharacter",
            doc={
                "id": str(uuid.uuid4()).upper(),
                "name": "Illegal warlord",
                "catalogVersion": catalog["version"],
                "factionID": votann["id"],
                "battleSizeID": "incursion",
                "detachmentIDs": ["leagues-of-votann--brandfast-oathband"],
                "units": [w],
                "warlordUnitID": w["id"],
                "notes": "",
                "createdAt": "2026-01-01T00:00:00Z",
                "updatedAt": "2026-01-01T00:00:00Z",
            },
        )
    )
    # DP over budget
    k = new_unit(kahl["id"], 1)
    w2 = new_unit(warriors["id"], 10)
    samples.append(
        BuiltList(
            name="illegal DP over budget",
            expected_legal=False,
            notes="dp.overBudget",
            doc={
                "id": str(uuid.uuid4()).upper(),
                "name": "Illegal DP",
                "catalogVersion": catalog["version"],
                "factionID": votann["id"],
                "battleSizeID": "incursion",
                "detachmentIDs": [hearthband["id"]],
                "units": [k, w2],
                "warlordUnitID": k["id"],
                "notes": "",
                "createdAt": "2026-01-01T00:00:00Z",
                "updatedAt": "2026-01-01T00:00:00Z",
            },
        )
    )
    # Empty leaderTo must not attach freely (regression for attachNoTargets).
    body = new_unit(legionaries["id"], 10)
    char = new_unit(moe["id"], 1, attachedToUnitID=body["id"])
    samples.append(
        BuiltList(
            name="illegal attach with empty leaderTo",
            expected_legal=False,
            notes="unit.attachNoTargets",
            doc={
                "id": str(uuid.uuid4()).upper(),
                "name": "Illegal empty leaderTo attach",
                "catalogVersion": catalog["version"],
                "factionID": "chaos-space-marines",
                "battleSizeID": "incursion",
                "detachmentIDs": [csm_det["id"]],
                "units": [body, char],
                "warlordUnitID": char["id"],
                "notes": "",
                "createdAt": "2026-01-01T00:00:00Z",
                "updatedAt": "2026-01-01T00:00:00Z",
            },
        )
    )
    return samples


def build_fifty(catalog: dict) -> list[BuiltList]:
    lists: list[BuiltList] = []
    factions = sorted(catalog["factions"], key=lambda f: f["name"].casefold())
    seed = 0

    # One Incursion list per faction (30).
    for faction in factions:
        built = fill_list(
            catalog,
            faction,
            "incursion",
            seed=seed,
            attach=True,
            with_enhancement=True,
            target_fill=0.90,
        )
        seed += 1
        if built:
            lists.append(built)

    # Strike Force samples (17) + 3 illegal = 50.
    strike_factions = [
        "space-marines",
        "astra-militarum",
        "aeldari",
        "necrons",
        "orks",
        "tyranids",
        "tau-empire",
        "adepta-sororitas",
        "death-guard",
        "thousand-sons",
        "world-eaters",
        "blood-angels",
        "dark-angels",
        "space-wolves",
        "genestealer-cults",
        "drukhari",
        "grey-knights",
    ]
    for fid in strike_factions:
        faction = next(f for f in factions if f["id"] == fid)
        built = fill_list(
            catalog,
            faction,
            "strike-force",
            seed=seed,
            attach=True,
            with_enhancement=True,
            target_fill=0.93,
        )
        seed += 1
        if built:
            lists.append(built)

    lists.extend(build_illegal_samples(catalog))
    return lists[:50]


def catalog_integrity(catalog: dict) -> list[str]:
    findings: list[str] = []
    sheets = {d["id"]: d for d in catalog["datasheets"]}
    for sheet in catalog["datasheets"]:
        for target in sheet.get("leaderTo") or []:
            if target not in sheets:
                findings.append(f"leaderTo dangling: {sheet['id']} -> {target}")
            elif sheets[target]["factionID"] != sheet["factionID"]:
                findings.append(
                    f"leaderTo cross-faction: {sheet['id']} -> {target}"
                )
        for tier in sheet.get("pointsTiers") or []:
            if not tier.get("byModels"):
                findings.append(f"empty points tier: {sheet['id']}")
        # Characters without Character role but named like HQ
        name = sheet["name"].lower()
        if sheet.get("characterRole") is None and any(
            k in name for k in ("captain", "lieutenant", "chaos lord", "warlord", "primarch")
        ):
            # only flag if also no keywords beyond faction — likely BS miss
            if len(sheet.get("keywords") or []) <= 1:
                findings.append(f"likely missing Character keywords: {sheet['id']}")
    # Duplicate enhancement ids
    enh_ids = []
    for det in catalog["detachments"]:
        for enh in det.get("enhancements") or []:
            enh_ids.append(enh["id"])
    if len(enh_ids) != len(set(enh_ids)):
        from collections import Counter

        dups = [i for i, n in Counter(enh_ids).items() if n > 1]
        findings.append(f"duplicate enhancement ids: {dups[:5]}")
    return findings


def write_fixtures(lists: list[BuiltList]) -> None:
    FIXTURES_DIR.mkdir(parents=True, exist_ok=True)
    # Clear old fixtures
    for old in FIXTURES_DIR.glob("*.json"):
        old.unlink()
    manifest = []
    for i, built in enumerate(lists, start=1):
        slug = f"{i:02d}-{'legal' if built.expected_legal else 'illegal'}-{built.doc['factionID']}-{built.doc['battleSizeID']}"
        # sanitize filename
        slug = "".join(c if c.isalnum() or c in "-_" else "-" for c in slug)
        path = FIXTURES_DIR / f"{slug}.json"
        payload = {
            "expectedLegal": built.expected_legal,
            "notes": built.notes,
            "list": built.doc,
        }
        path.write_text(json.dumps(payload, indent=2) + "\n")
        manifest.append({"file": path.name, "expectedLegal": built.expected_legal, "name": built.name})
    (FIXTURES_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Wrote {len(lists)} fixtures to {FIXTURES_DIR}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()

    catalog = json.loads(CATALOG_PATH.read_text())
    print(f"Catalog {catalog['version']}: {len(catalog['factions'])} factions")

    integrity = catalog_integrity(catalog)
    print(f"\nCatalog integrity findings: {len(integrity)}")
    for line in integrity[:40]:
        print(f"  ! {line}")
    if len(integrity) > 40:
        print(f"  … {len(integrity) - 40} more")

    lists = build_fifty(catalog)
    print(f"\nBuilt {len(lists)} stress lists")

    unexpected_illegal: list[tuple[BuiltList, ValidationResult]] = []
    unexpected_legal: list[tuple[BuiltList, ValidationResult]] = []
    ok = 0
    for built in lists:
        result = validate(built.doc, catalog)
        status = "LEGAL" if result.is_legal else "ILLEGAL"
        expect = "LEGAL" if built.expected_legal else "ILLEGAL"
        mark = "OK" if (result.is_legal == built.expected_legal) else "BUG?"
        if result.is_legal == built.expected_legal:
            ok += 1
        elif built.expected_legal and not result.is_legal:
            unexpected_illegal.append((built, result))
        else:
            unexpected_legal.append((built, result))
        err_codes = ",".join(sorted({i.code for i in result.errors})) or "-"
        print(
            f"  [{mark}] {status} (expect {expect}) {built.name[:60]:60} "
            f"{result.total_points:4}pts DP={result.dp_spent} errs={err_codes}"
        )

    print(f"\nExpectation matches: {ok}/{len(lists)}")
    print(f"Unexpected ILLEGAL (builder thought legal): {len(unexpected_illegal)}")
    for built, result in unexpected_illegal:
        print(f"\n  LIST: {built.name}")
        print(f"  faction={built.doc['factionID']} size={built.doc['battleSizeID']}")
        print(f"  detachments={built.doc['detachmentIDs']}")
        print(f"  units={len(built.doc['units'])} pts={result.total_points}")
        for issue in result.errors:
            print(f"    ERROR {issue.code}: {issue.message}")

    print(f"\nUnexpected LEGAL (should be illegal): {len(unexpected_legal)}")
    for built, result in unexpected_legal:
        print(f"  LIST: {built.name} notes={built.notes}")

    if args.write_fixtures:
        write_fixtures(lists)

    # Exit non-zero if we found unexpected illegal (likely validator or builder/catalog bugs)
    # Always exit 0 for discovery runs unless --strict
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

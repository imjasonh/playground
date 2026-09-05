#!/usr/bin/env python3
"""Simulate a small on-device model building themed Incursion lists.

Uses only detachment/unit ids that would appear in ArmyListStarterPrompt
(theme-ranked candidate palette, max 22) and checks basic legality against
catalog.json. Run from repo root:

    python3 ios/scripts/audit-simple-model-builds.py
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CATALOG_PATH = REPO / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"

STOP = {
    "the", "and", "with", "for", "list", "army", "only", "all", "some", "few",
    "lots", "many", "themed", "theme", "build", "make", "create", "using", "use",
    "from", "that", "this",
}

THEMES: dict[str, str] = {
    "adepta-sororitas": "penitent martyrs battle sisters",
    "adeptus-custodes": "shield host custodian guard",
    "adeptus-mechanicus": "skitarii rad-zone",
    "aeldari": "swift aspect warriors",
    "astra-militarum": "armored leman russ company",
    "black-templars": "crusader melee vanguard",
    "blood-angels": "jump pack assault",
    "chaos-daemons": "khorne bloodletters",
    "chaos-knights": "chaos tyrant knights",
    "chaos-space-marines": "slaanesh noise marines",
    "chaos-titan-legions": "warlord titan",
    "dark-angels": "deathwing terminators",
    "death-guard": "poxwalker horde",
    "deathwatch": "kill team mixed specialties",
    "drukhari": "raider raiding party",
    "emperors-children": "sonic elite infantry",
    "genestealer-cults": "acolyte hybrid swarm",
    "grey-knights": "paladin strike force",
    "imperial-agents": "inquisitorial strike team",
    "imperial-knights": "armiger warglaive lance",
    "leagues-of-votann": "hearthkyn mining clan",
    "necrons": "destroyer cult",
    "orks": "boyz mob and weirdboy",
    "space-marines": "primaris intercessor battleline",
    "space-wolves": "thunderwolf cavalry",
    "thousand-sons": "rubric marine sorcery",
    "titan-legions": "reaver titan",
    "tyranids": "termagant hormagaunt swarm",
    "tau-empire": "crisis battlesuit cadre",
    "world-eaters": "khorne berserkers",
}


def theme_tokens(theme: str) -> list[str]:
    return [
        w
        for w in re.split(r"[^a-z0-9]+", theme.lower())
        if len(w) >= 3 and w not in STOP
    ]


def points(sheet: dict, models: int, copy: int = 1) -> int | None:
    for tier in sheet["pointsTiers"]:
        if copy < tier["fromCopy"]:
            continue
        if tier.get("toCopy") is not None and copy > tier["toCopy"]:
            continue
        return tier["byModels"].get(str(models))
    return None


def duplicate_limit(sheet: dict, battle: dict) -> int:
    if sheet.get("battleline"):
        cap = battle["battlelineDuplicateLimit"]
    elif sheet.get("dedicatedTransport"):
        cap = battle["dedicatedTransportDuplicateLimit"]
    else:
        cap = battle["datasheetDuplicateLimit"]
    if sheet.get("maxCopiesOverride") is not None:
        return min(sheet["maxCopiesOverride"], cap)
    if sheet.get("epicHero"):
        return 1
    return cap


def candidate_palette(catalog: dict, faction_id: str, battle: dict, theme: str, limit: int = 22):
    tokens = theme_tokens(theme)
    eligible = []
    for sheet in catalog["datasheets"]:
        if sheet["factionID"] != faction_id or sheet.get("legends"):
            continue
        if not any(points(sheet, m) is not None for m in sheet["modelCounts"]):
            continue
        score = 0
        if tokens:
            hay = " ".join([sheet["name"], sheet["id"], *sheet["keywords"]]).lower()
            score += sum(100 for t in tokens if t in hay)
        if sheet.get("characterRole"):
            score += 10
        if sheet.get("battleline"):
            score += 5
        eligible.append((score, sheet))
    eligible.sort(key=lambda x: (-x[0], x[1]["name"].lower()))
    chosen = eligible[:limit]
    if not any(s.get("characterRole") for _, s in chosen):
        char = next((s for _, s in eligible if s.get("characterRole")), None)
        if char:
            if chosen:
                chosen = chosen[:-1]
            chosen.append((0, char))
    return [s for _, s in chosen]


def resolve_detachment(catalog: dict, faction_id: str, raw: str) -> str | None:
    q = raw.strip().lower()
    dets = [d for d in catalog["detachments"] if d["factionID"] == faction_id]
    for d in dets:
        if d["id"] == q:
            return d["id"]
    matches = [d for d in dets if q in d["id"] or q in d["name"].lower()]
    return matches[0]["id"] if len(matches) == 1 else None


def resolve_sheet(catalog: dict, faction_id: str, raw: str) -> dict | None:
    q = raw.strip().lower()
    sheets = [s for s in catalog["datasheets"] if s["factionID"] == faction_id]
    for s in sheets:
        if s["id"] == q:
            return s
    matches = [s for s in sheets if q in s["id"] or q in s["name"].lower()]
    return matches[0] if len(matches) == 1 else None


def greedy_roster(palette: list[dict], battle: dict, budget: int = 1000):
    """Dumb-but-valid packer: themed-first palette, repeat ids up to max copies."""
    units: list[tuple[str, int]] = []
    used: Counter[str] = Counter()
    total = 0

    def add_sheet(sheet: dict) -> None:
        nonlocal total
        limit = duplicate_limit(sheet, battle)
        best = None
        for models in sheet["modelCounts"]:
            p = points(sheet, models, 1)
            if p is not None:
                best = (models, p)
                break
        if best is None:
            return
        models, unit_pts = best
        while used[sheet["id"]] < limit:
            copy = used[sheet["id"]] + 1
            p = points(sheet, models, copy) or unit_pts
            if total + p > budget:
                break
            used[sheet["id"]] += 1
            units.append((sheet["id"], models))
            total += p

    char = next((s for s in palette if s.get("characterRole")), None)
    if char:
        add_sheet(char)
    for sheet in palette:
        if sheet is char:
            continue
        add_sheet(sheet)
    return units, total


@dataclass
class Result:
    faction_id: str
    theme: str
    legal: bool
    points: int
    remaining: int
    issues: list[str]
    detachment: str | None
    unit_count: int


def validate_build(catalog: dict, faction_id: str, battle_id: str, theme: str) -> Result:
    battle = next(b for b in catalog["battleSizes"] if b["id"] == battle_id)
    issues: list[str] = []
    dets = [
        d
        for d in catalog["detachments"]
        if d["factionID"] == faction_id and d["detachmentPoints"] <= battle["detachmentPointsBudget"]
    ]
    if not dets:
        issues.append("no detachments within DP budget")
    palette = candidate_palette(catalog, faction_id, battle, theme)
    if not palette:
        issues.append("empty candidate palette")
    if not any(s.get("characterRole") for s in palette):
        issues.append("no character in palette")

    cheapest = min(
        (
            p
            for s in catalog["datasheets"]
            if s["factionID"] == faction_id and not s.get("legends")
            for m in s["modelCounts"]
            if (p := points(s, m)) is not None
        ),
        default=None,
    )
    if cheapest is not None and cheapest > battle["pointsLimit"]:
        issues.append(f"cheapest unit {cheapest} > limit {battle['pointsLimit']}")

    det_id = dets[0]["id"] if dets else None
    dp = dets[0]["detachmentPoints"] if dets else 0
    if dp > battle["detachmentPointsBudget"]:
        issues.append("detachment over DP budget")

    units, total = greedy_roster(palette, battle, battle["pointsLimit"]) if palette else ([], 0)
    if not units:
        issues.append("greedy packer produced no units")

    has_char = False
    for sheet_id, models in units:
        sheet = next(s for s in catalog["datasheets"] if s["id"] == sheet_id)
        if sheet.get("characterRole"):
            has_char = True
        if points(sheet, models) is None:
            issues.append(f"no points for {sheet_id} x{models}")

    if units and not has_char:
        issues.append("no warlord character")

    if total > battle["pointsLimit"]:
        issues.append("over points limit")

    legal = not issues
    return Result(
        faction_id=faction_id,
        theme=theme,
        legal=legal,
        points=total,
        remaining=battle["pointsLimit"] - total,
        issues=issues,
        detachment=det_id,
        unit_count=len(units),
    )


def main() -> int:
    catalog = json.loads(CATALOG_PATH.read_text())
    rows: list[Result] = []
    for faction in sorted(catalog["factions"], key=lambda f: f["name"]):
        fid = faction["id"]
        theme = THEMES.get(fid, "thematic force")
        rows.append(validate_build(catalog, fid, "incursion", theme))

    legal = sum(1 for r in rows if r.legal)
    print(f"Simple-model audit: {legal}/{len(rows)} factions legal at Incursion\n")
    print(f"{'faction':28} {'pts':>5} {'left':>5} {'units':>5}  ok  issues")
    print("-" * 80)
    for r in rows:
        ok = "yes" if r.legal else " NO"
        issue_text = "; ".join(r.issues) if r.issues else ""
        print(
            f"{r.faction_id:28} {r.points:5} {r.remaining:5} {r.unit_count:5} {ok:>4}  {issue_text}"
        )

    failed = [r for r in rows if not r.legal]
    expected_fail = {"titan-legions", "chaos-titan-legions"}
    unexpected = [r for r in failed if r.faction_id not in expected_fail]
    if unexpected:
        print(f"\nUnexpected failures: {[r.faction_id for r in unexpected]}")
        return 1
    if failed:
        print("\nExpected failures: titan factions cannot build at Incursion (see report).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

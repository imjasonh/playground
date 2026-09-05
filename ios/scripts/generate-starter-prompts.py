#!/usr/bin/env python3
"""Emit the exact ArmyListStarterPrompt our app sends, one per faction.

Mirrors ArmyListStarterPrompt.prompt (palette ranking, pts@models | max columns,
DP-filtered detachments, closing instruction) so a simple LLM sees precisely
what the on-device model sees. Writes JSON: [{faction, theme, battleSize, prompt}].

Run from repo root:
    python3 ios/scripts/generate-starter-prompts.py --out /tmp/starter-prompts.json
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CATALOG_PATH = REPO / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"

STOP = {
    "the", "and", "with", "for", "list", "army", "only", "all", "some", "few",
    "lots", "many", "themed", "theme", "build", "make", "create", "using", "use",
    "from", "that", "this",
}

THEMES = {
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


def tokens(theme):
    return [w for w in re.split(r"[^a-z0-9]+", theme.lower()) if len(w) >= 3 and w not in STOP]


def points(sheet, models, copy=1):
    for tier in sheet["pointsTiers"]:
        if copy < tier["fromCopy"]:
            continue
        if tier.get("toCopy") is not None and copy > tier["toCopy"]:
            continue
        return tier["byModels"].get(str(models))
    return None


def dup_limit(sheet, battle):
    if sheet.get("battleline"):
        cap = battle["battlelineDuplicateLimit"]
    elif sheet.get("dedicatedTransport"):
        cap = battle["dedicatedTransportDuplicateLimit"]
    else:
        cap = battle["datasheetDuplicateLimit"]
    if sheet.get("epicHero"):
        cap = min(cap, 1)
    if sheet.get("maxCopiesOverride") is not None:
        return min(sheet["maxCopiesOverride"], cap)
    return cap


def candidate_line(sheet, battle):
    flags = []
    if sheet.get("characterRole"):
        flags.append("Character")
    if sheet.get("battleline"):
        flags.append("Battleline")
    if sheet.get("dedicatedTransport"):
        flags.append("Transport")
    role = ",".join(flags) if flags else "-"
    opts = ",".join(
        f"{points(sheet, m)}@{m}" for m in sheet["modelCounts"] if points(sheet, m) is not None
    )
    return f"{sheet['id']} | {sheet['name']} | {opts} | {role} | {dup_limit(sheet, battle)}"


def palette(catalog, fid, battle, theme, limit=22):
    tk = tokens(theme)
    elig = []
    for s in catalog["datasheets"]:
        if s["factionID"] != fid or s.get("legends"):
            continue
        if not any(points(s, m) is not None for m in s["modelCounts"]):
            continue
        score = 0
        if tk:
            hay = " ".join([s["name"], s["id"], *s["keywords"]]).lower()
            score += sum(100 for t in tk if t in hay)
        if s.get("characterRole"):
            score += 10
        if s.get("battleline"):
            score += 5
        elig.append((score, s))
    elig.sort(key=lambda x: (-x[0], x[1]["name"].lower()))
    chosen = [s for _, s in elig[:limit]]
    if not any(s.get("characterRole") for s in chosen):
        ch = next((s for _, s in elig if s.get("characterRole")), None)
        if ch:
            if chosen:
                chosen = chosen[:-1]
            chosen.append(ch)
    return chosen


def build_prompt(catalog, fid, battle_id, theme):
    battle = next(b for b in catalog["battleSizes"] if b["id"] == battle_id)
    fname = next((f["name"] for f in catalog["factions"] if f["id"] == fid), fid)
    limit = battle["pointsLimit"]
    dp = battle["detachmentPointsBudget"]
    lines = [f"Build one {fname} army list for {battle['name']} ({limit} pts, {dp} DP budget)."]
    if theme.strip():
        lines.append(f"Theme: {theme}. Favor units that fit it and name the list accordingly.")
    dets = sorted(
        (d for d in catalog["detachments"] if d["factionID"] == fid and d["detachmentPoints"] <= dp),
        key=lambda d: d["name"].lower(),
    )
    if not dets:
        lines += ["", f"No detachments fit the {dp} DP budget for this battle size."]
    else:
        lines += ["", "Detachments (id | name | DP):"]
        for d in dets[:12]:
            lines.append(f"{d['id']} | {d['name']} | {d['detachmentPoints']} DP")
    lines += ["", "Units (id | name | pts@models | role | max):"]
    for s in palette(catalog, fid, battle, theme):
        lines.append(candidate_line(s, battle))
    lines += [
        "",
        (
            "Call applyRosterPlan exactly once: pick one detachment id above within the DP budget, "
            f"and units from the ids above. Get as close to {limit} pts as you can — "
            "keep adding units until no listed unit fits the points that remain. "
            "Use pts@models sizes and max copy counts from the table; repeat an id to field another copy. "
            "Include at least one Character for the Warlord."
        ),
    ]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="/tmp/starter-prompts.json")
    ap.add_argument("--battle-size", default="incursion")
    args = ap.parse_args()
    catalog = json.loads(CATALOG_PATH.read_text())
    out = []
    for faction in sorted(catalog["factions"], key=lambda f: f["name"]):
        fid = faction["id"]
        theme = THEMES.get(fid, "thematic force")
        out.append(
            {
                "faction": fid,
                "factionName": faction["name"],
                "theme": theme,
                "battleSize": args.battle_size,
                "prompt": build_prompt(catalog, fid, args.battle_size, theme),
            }
        )
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(f"Wrote {len(out)} starter prompts to {args.out}")


if __name__ == "__main__":
    main()

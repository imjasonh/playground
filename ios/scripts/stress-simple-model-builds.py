#!/usr/bin/env python3
"""Stress many simple-model builds and grade them like the stronger model.

Generates lists for every faction across both battle sizes, several themes, and
several weak-model strategies, using only what ArmyListStarterPrompt exposes
(theme-ranked palette, pts@models, max copies, DP-filtered detachments) and one
applyRosterPlan-style call.

For each list it grades legality with a faithful replica of ArmyListValidator's
construction rules, plus fill efficiency and theme adherence — the axes a
stronger model would judge. It compares today's accept-all applyRosterPlan
against a proposed clamp (drop over-cap copies, trim trailing over-limit units)
to quantify which tool fix helps weak models most.

Run from repo root:  python3 ios/scripts/stress-simple-model-builds.py
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CATALOG_PATH = REPO / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"

STOP = {
    "the", "and", "with", "for", "list", "army", "only", "all", "some", "few",
    "lots", "many", "themed", "theme", "build", "make", "create", "using", "use",
    "from", "that", "this",
}

# A handful of themes per faction: one lore-narrow, one broad, one off-catalog
# phrasing, to stress theme→keyword matching the way varied users would.
THEMES: dict[str, list[str]] = {
    "adepta-sororitas": ["penitent martyrs", "battle sisters bolter", "seraphim angels"],
    "adeptus-custodes": ["shield host guard", "custodian wardens", "grav-tank spearhead"],
    "adeptus-mechanicus": ["skitarii rad-zone", "kataphron breachers", "onager dunecrawler"],
    "aeldari": ["aspect warriors", "wraith constructs", "guardian defenders"],
    "astra-militarum": ["armored leman russ", "infantry regiment", "tank commander"],
    "black-templars": ["crusader melee vanguard", "sword brethren", "neophyte zealots"],
    "blood-angels": ["jump pack assault", "death company", "sanguinary guard"],
    "chaos-daemons": ["khorne bloodletters", "nurgle plague", "tzeentch horrors"],
    "chaos-knights": ["tyrant knights", "war dogs pack", "wretched abominations"],
    "chaos-space-marines": ["noise marines", "chaos terminators", "cultist horde"],
    "chaos-titan-legions": ["warlord titan", "reaver maniple", "warhound pack"],
    "dark-angels": ["deathwing terminators", "ravenwing bikes", "intercessor line"],
    "death-guard": ["poxwalker horde", "plague marines", "death shroud"],
    "deathwatch": ["kill team", "veteran squads", "terminator strike"],
    "drukhari": ["raider raiding party", "wych cult", "kabalite warriors"],
    "emperors-children": ["sonic elite", "noise infantry", "flawless host"],
    "genestealer-cults": ["acolyte swarm", "neophyte conscripts", "aberrant brood"],
    "grey-knights": ["paladin strike", "terminator justicars", "purifier squad"],
    "imperial-agents": ["inquisitorial team", "assassin operatives", "agent retinue"],
    "imperial-knights": ["armiger warglaive", "questoris lance", "noble titans"],
    "leagues-of-votann": ["hearthkyn clan", "hernkyn scouts", "sagitaur convoy"],
    "necrons": ["destroyer cult", "warrior phalanx", "canoptek swarm"],
    "orks": ["boyz mob", "speed freeks", "weirdboy waaagh"],
    "space-marines": ["intercessor battleline", "gladius terminators", "vanguard phobos"],
    "space-wolves": ["thunderwolf cavalry", "blood claws", "grey hunters"],
    "thousand-sons": ["rubric marines", "sorcery cabal", "scarab occult"],
    "titan-legions": ["reaver titan", "warlord battlegroup", "warhound pack"],
    "tyranids": ["termagant swarm", "hormagaunt brood", "monstrous bioforms"],
    "tau-empire": ["crisis battlesuit", "fire warrior cadre", "riptide support"],
    "world-eaters": ["khorne berserkers", "blood host", "eightbound melee"],
}


def theme_tokens(theme: str) -> list[str]:
    return [w for w in re.split(r"[^a-z0-9]+", theme.lower()) if len(w) >= 3 and w not in STOP]


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
    if sheet.get("epicHero"):
        cap = min(cap, 1)
    if sheet.get("maxCopiesOverride") is not None:
        return min(sheet["maxCopiesOverride"], cap)
    return cap


def cheapest_size(sheet: dict) -> tuple[int, int] | None:
    for models in sheet["modelCounts"]:
        p = points(sheet, models, 1)
        if p is not None:
            return models, p
    return None


def palette(catalog: dict, faction_id: str, theme: str, limit: int = 22) -> list[dict]:
    tokens = theme_tokens(theme)
    eligible = []
    for sheet in catalog["datasheets"]:
        if sheet["factionID"] != faction_id or sheet.get("legends"):
            continue
        if cheapest_size(sheet) is None:
            continue
        score = 0
        if tokens:
            hay = " ".join([sheet["name"], sheet["id"], *sheet["keywords"], *sheet.get("themeKeywords", [])]).lower()
            score += sum(100 for t in tokens if t in hay)
        if sheet.get("characterRole"):
            score += 10
        if sheet.get("battleline"):
            score += 5
        eligible.append((score, sheet))
    eligible.sort(key=lambda x: (-x[0], x[1]["name"].lower()))
    chosen = [s for _, s in eligible[:limit]]
    if not any(s.get("characterRole") for s in chosen):
        char = next((s for _, s in eligible if s.get("characterRole")), None)
        if char:
            if chosen:
                chosen = chosen[:-1]
            chosen.append(char)
    themed_ids = {s["id"] for score, s in eligible[:limit] if score >= 100}
    for s in chosen:
        s["_themed"] = s["id"] in themed_ids
    return chosen


def detachment_for(catalog: dict, faction_id: str, battle: dict) -> dict | None:
    dets = [
        d
        for d in catalog["detachments"]
        if d["factionID"] == faction_id and d["detachmentPoints"] <= battle["detachmentPointsBudget"]
    ]
    return dets[0] if dets else None


# --- Weak-model strategies: return an ordered list of (sheet, models) picks ----
# Each models what a simple model might do reading only the palette prompt.


def strat_char_first(pal, battle, budget):
    """Best case: put a Character first, then pack by palette (themed) order."""
    picks, used, total = [], Counter(), 0
    char = next((s for s in pal if s.get("characterRole")), None)
    order = ([char] if char else []) + [s for s in pal if s is not char]
    for sheet in order:
        cap = duplicate_limit(sheet, battle)
        size = cheapest_size(sheet)
        if not size:
            continue
        models, base = size
        while used[sheet["id"]] < cap:
            copy = used[sheet["id"]] + 1
            p = points(sheet, models, copy) or base
            if total + p > budget:
                break
            used[sheet["id"]] += 1
            picks.append((sheet, models))
            total += p
    return picks


def strat_palette_order(pal, battle, budget):
    """Naive: follow palette order, may never add a Character."""
    picks, used, total = [], Counter(), 0
    for sheet in pal:
        cap = duplicate_limit(sheet, battle)
        size = cheapest_size(sheet)
        if not size:
            continue
        models, base = size
        while used[sheet["id"]] < cap:
            copy = used[sheet["id"]] + 1
            p = points(sheet, models, copy) or base
            if total + p > budget:
                break
            used[sheet["id"]] += 1
            picks.append((sheet, models))
            total += p
    return picks


def strat_ignore_max(pal, battle, budget):
    """Ignores the max column: spams the first battleline past its copy cap."""
    picks, total = [], 0
    char = next((s for s in pal if s.get("characterRole")), None)
    if char:
        size = cheapest_size(char)
        if size:
            picks.append((char, size[0]))
            total += size[1]
    spam = next((s for s in pal if s.get("battleline")), None) or (pal[0] if pal else None)
    if spam:
        size = cheapest_size(spam)
        if size:
            models, base = size
            copy = 0
            while total + base <= budget:
                copy += 1
                p = points(spam, models, copy) or base
                if total + p > budget:
                    break
                picks.append((spam, models))
                total += p
    return picks


def strat_overshoot(pal, battle, budget):
    """Aims high and overshoots: keeps adding themed units past the limit once."""
    picks, used, total = [], Counter(), 0
    char = next((s for s in pal if s.get("characterRole")), None)
    order = ([char] if char else []) + [s for s in pal if s is not char]
    for sheet in order:
        cap = duplicate_limit(sheet, battle)
        size = cheapest_size(sheet)
        if not size:
            continue
        models, base = size
        while used[sheet["id"]] < cap:
            used[sheet["id"]] += 1
            picks.append((sheet, models))
            total += points(sheet, models, used[sheet["id"]]) or base
            if total >= budget:  # one unit over is allowed to slip in
                return picks
    return picks


def strat_theme_pure(pal, battle, budget):
    """Only themed units + one Character; may under-fill when theme is narrow."""
    picks, used, total = [], Counter(), 0
    char = next((s for s in pal if s.get("characterRole")), None)
    if char:
        size = cheapest_size(char)
        if size:
            picks.append((char, size[0]))
            used[char["id"]] += 1
            total += size[1]
    for sheet in pal:
        if not sheet.get("_themed") or sheet is char:
            continue
        cap = duplicate_limit(sheet, battle)
        size = cheapest_size(sheet)
        if not size:
            continue
        models, base = size
        while used[sheet["id"]] < cap:
            copy = used[sheet["id"]] + 1
            p = points(sheet, models, copy) or base
            if total + p > budget:
                break
            used[sheet["id"]] += 1
            picks.append((sheet, models))
            total += p
    return picks


STRATEGIES = {
    "char_first": strat_char_first,
    "palette_order": strat_palette_order,
    "ignore_max": strat_ignore_max,
    "overshoot": strat_overshoot,
    "theme_pure": strat_theme_pure,
}


# --- applyRosterPlan resolution: today (accept-all) vs proposed (clamp) --------


def resolve_accept_all(picks, battle, budget):
    return list(picks)


def resolve_clamp(picks, battle, budget):
    """Proposed tool behavior: drop over-cap copies, trim trailing over-limit."""
    kept, used, total = [], Counter(), 0
    for sheet, models in picks:
        cap = duplicate_limit(sheet, battle)
        if used[sheet["id"]] >= cap:
            continue  # over copy cap → drop
        copy = used[sheet["id"]] + 1
        p = points(sheet, models, copy) or (cheapest_size(sheet) or (models, 0))[1]
        if total + p > budget:
            continue  # would overshoot → skip this unit, keep trying smaller ones
        used[sheet["id"]] += 1
        kept.append((sheet, models))
        total += p
    return kept


# --- Stronger-model grading ----------------------------------------------------


@dataclass
class Grade:
    legal: bool
    points: int
    limit: int
    themed_points: int
    warlord: bool
    issues: list[str] = field(default_factory=list)

    @property
    def fill(self) -> float:
        return self.points / self.limit if self.limit else 0.0

    @property
    def theme_share(self) -> float:
        return self.themed_points / self.points if self.points else 0.0


def grade(picks, catalog, faction_id, battle, detach) -> Grade:
    issues: list[str] = []
    budget = battle["pointsLimit"]
    total = 0
    themed = 0
    used = Counter()
    warlord = False
    for sheet, models in picks:
        cap = duplicate_limit(sheet, battle)
        used[sheet["id"]] += 1
        copy = used[sheet["id"]]
        if copy > cap:
            issues.append(f"copy cap {sheet['id']}")
        if models not in sheet["modelCounts"]:
            issues.append(f"model count {sheet['id']}")
        p = points(sheet, models, copy)
        if p is None:
            issues.append(f"no points {sheet['id']}")
            p = 0
        total += p
        if sheet.get("_themed"):
            themed += p
        if sheet.get("characterRole"):
            warlord = True
    if detach is None:
        issues.append("no detachment")
    elif detach["detachmentPoints"] > battle["detachmentPointsBudget"]:
        issues.append("dp over budget")
    if not warlord:
        issues.append("no warlord")
    if total > budget:
        issues.append("over points")
    if not picks:
        issues.append("empty")
    legal = not issues
    return Grade(legal, total, budget, themed, warlord, issues)


def main() -> int:
    catalog = json.loads(CATALOG_PATH.read_text())
    battles = {b["id"]: b for b in catalog["battleSizes"]}
    factions = sorted(catalog["factions"], key=lambda f: f["name"])
    titan = {"titan-legions", "chaos-titan-legions"}

    # (resolution, strategy) -> counters
    tally: dict[tuple[str, str], Counter] = defaultdict(Counter)
    fills: dict[tuple[str, str], list[float]] = defaultdict(list)
    themes_share: dict[tuple[str, str], list[float]] = defaultdict(list)
    issue_counts: Counter = Counter()
    total_lists = 0

    for faction in factions:
        fid = faction["id"]
        if fid in titan:
            continue  # correctly gated before the model runs
        for bid, battle in battles.items():
            detach = detachment_for(catalog, fid, battle)
            for theme in THEMES.get(fid, ["thematic force"]):
                pal = palette(catalog, fid, theme)
                for sname, strat in STRATEGIES.items():
                    picks = strat(pal, battle, battle["pointsLimit"])
                    total_lists += 1
                    for rname, resolve in (("accept_all", resolve_accept_all), ("clamp", resolve_clamp)):
                        resolved = resolve(picks, battle, battle["pointsLimit"])
                        g = grade(resolved, catalog, fid, battle, detach)
                        key = (rname, sname)
                        tally[key]["n"] += 1
                        tally[key]["legal"] += int(g.legal)
                        fills[key].append(g.fill)
                        if g.points:
                            themes_share[key].append(g.theme_share)
                        if rname == "accept_all":
                            for code in g.issues:
                                issue_counts[code.split()[0]] += 1

    print(f"Stress run: {total_lists} simple-model builds ({len(factions) - len(titan)} factions × "
          f"{len(battles)} sizes × up-to-3 themes × {len(STRATEGIES)} strategies)\n")

    def pct(key):
        n = tally[key]["n"] or 1
        return 100.0 * tally[key]["legal"] / n

    def avg(xs):
        return sum(xs) / len(xs) if xs else 0.0

    print(f"{'strategy':16} {'accept-all legal':>17} {'clamp legal':>12} {'fill(clamp)':>12} {'theme(clamp)':>13}")
    print("-" * 74)
    for sname in STRATEGIES:
        a = ("accept_all", sname)
        c = ("clamp", sname)
        print(
            f"{sname:16} {pct(a):16.0f}% {pct(c):11.0f}% "
            f"{avg(fills[c]) * 100:11.0f}% {avg(themes_share[c]) * 100:12.0f}%"
        )

    print("\nTop accept-all failure modes (issue → count):")
    for code, n in issue_counts.most_common(8):
        print(f"  {code:20} {n}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Execute simple-LLM roster plans through faithful app tools, then assess.

Input: JSON array of plans the LLM produced from the starter prompts, each
    {faction, battleSize, detachments, units, name}
where `units` is "id:models,id:models,..." exactly as passed to applyRosterPlan.

This runs each plan through a faithful replica of applyRosterPlan (including the
shipped clamp) and ArmyListValidator's core legality, then grades it the way a
stronger model would: legal, points/fill, theme share, warlord, and — crucially
— whether the LLM referenced ids that were NOT in the prompt palette
(hallucination) or omitted a detachment. Those are tool/prompt gaps, not packing
bugs, because the app calls tools on the model's judgement rather than computing
a roster in code.

Run from repo root:
    python3 ios/scripts/execute-and-assess-plans.py --plans /tmp/simple-model-plans.json
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

import importlib.util

REPO = Path(__file__).resolve().parents[2]
CATALOG_PATH = REPO / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"

# Reuse palette/points/dup_limit from the generator so "offered ids" match the
# prompt exactly.
_spec = importlib.util.spec_from_file_location(
    "gen", REPO / "ios/scripts/generate-starter-prompts.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def resolve_detachment(catalog, fid, raw):
    q = raw.strip().lower()
    dets = [d for d in catalog["detachments"] if d["factionID"] == fid]
    for d in dets:
        if d["id"] == q:
            return d
    m = [d for d in dets if q and (q in d["id"] or q in d["name"].lower())]
    return m[0] if len(m) == 1 else None


def resolve_sheet(catalog, fid, raw):
    q = raw.strip().lower()
    sheets = [s for s in catalog["datasheets"] if s["factionID"] == fid]
    for s in sheets:
        if s["id"] == q:
            return s
    m = [s for s in sheets if q and (q in s["id"] or q in s["name"].lower())]
    return m[0] if len(m) == 1 else None


def apply_roster_plan(catalog, fid, battle, det_csv, units_csv):
    """Faithful applyRosterPlan: resolve + clamp copies/points, pick warlord."""
    notes = {"unknown_units": [], "unknown_dets": [], "over_cap": 0, "over_limit": 0}
    det_ids = []
    for raw in [x.strip() for x in det_csv.split(",") if x.strip()]:
        d = resolve_detachment(catalog, fid, raw)
        if d and d["id"] not in det_ids:
            det_ids.append(d["id"])
        elif not d:
            notes["unknown_dets"].append(raw)

    resolved = []
    for raw in [x.strip() for x in units_csv.split(",") if x.strip()]:
        parts = raw.split(":", 1)
        s = resolve_sheet(catalog, fid, parts[0])
        if not s:
            notes["unknown_units"].append(parts[0])
            continue
        models = s["modelCounts"][0]
        if len(parts) == 2:
            try:
                want = int(parts[1])
                if want in s["modelCounts"]:
                    models = want
            except ValueError:
                pass
        resolved.append((s, models))

    kept, copies, total = [], Counter(), 0
    for s, models in resolved:
        cap = gen.dup_limit(s, battle)
        if copies[s["id"]] >= cap:
            notes["over_cap"] += 1
            continue
        copy = copies[s["id"]] + 1
        cost = gen.points(s, models, copy) or gen.points(s, s["modelCounts"][0], copy)
        if cost is None:
            continue
        if total + cost > battle["pointsLimit"]:
            notes["over_limit"] += 1
            continue
        copies[s["id"]] = copy
        kept.append((s, models))
        total += cost
    return det_ids, kept, total, notes


def assess(catalog, plan):
    fid = plan["faction"]
    battle = next(b for b in catalog["battleSizes"] if b["id"] == plan.get("battleSize", "incursion"))
    theme = gen.THEMES.get(fid, "")
    offered = {s["id"] for s in gen.palette(catalog, fid, battle, theme)}
    offered_dets = {
        d["id"]
        for d in catalog["detachments"]
        if d["factionID"] == fid and d["detachmentPoints"] <= battle["detachmentPointsBudget"]
    }
    themed = set()
    tk = gen.tokens(theme)
    for s in catalog["datasheets"]:
        if s["factionID"] != fid:
            continue
        hay = " ".join([s["name"], s["id"], *s["keywords"]]).lower()
        if tk and any(t in hay for t in tk):
            themed.add(s["id"])

    det_ids, kept, total, notes = apply_roster_plan(
        catalog, fid, battle, plan.get("detachments", ""), plan.get("units", "")
    )

    issues = []
    if not det_ids:
        issues.append("no detachment resolved")
    warlord = any(s.get("characterRole") for s, _ in kept)
    if not warlord:
        issues.append("no warlord character")
    if not kept:
        issues.append("empty roster")

    # Hallucination signals (tool/prompt gaps).
    off_palette_units = [u for u in notes["unknown_units"]]
    used_ids = [s["id"] for s, _ in kept]
    not_offered = [uid for uid in used_ids if uid not in offered]
    det_not_offered = [d for d in det_ids if d not in offered_dets]

    themed_pts = 0
    for s, models in kept:
        c = Counter()
        c[s["id"]] += 1
        p = gen.points(s, models, 1) or 0
        if s["id"] in themed:
            themed_pts += p
    fill = total / battle["pointsLimit"] if battle["pointsLimit"] else 0
    theme_share = themed_pts / total if total else 0

    legal = not issues and total <= battle["pointsLimit"]
    return {
        "faction": fid,
        "legal": legal,
        "points": total,
        "fill": fill,
        "theme_share": theme_share,
        "warlord": warlord,
        "units": len(kept),
        "unknown_units": off_palette_units,
        "units_off_palette": not_offered,
        "detachment_off_palette": det_not_offered,
        "clamped_over_cap": notes["over_cap"],
        "clamped_over_limit": notes["over_limit"],
        "issues": issues,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--plans", default="/tmp/simple-model-plans.json")
    args = ap.parse_args()
    catalog = json.loads(CATALOG_PATH.read_text())
    plans = json.loads(Path(args.plans).read_text())
    results = [assess(catalog, p) for p in plans]

    legal = sum(1 for r in results if r["legal"])
    print(f"Simple-LLM builds executed through app tools: {legal}/{len(results)} legal\n")
    hdr = f"{'faction':28} {'ok':>3} {'pts':>5} {'fill':>5} {'thm':>5} {'wl':>3} notes"
    print(hdr)
    print("-" * len(hdr))
    agg = Counter()
    for r in results:
        note = []
        if r["unknown_units"]:
            note.append(f"unknown={r['unknown_units']}")
            agg["hallucinated unit ids"] += 1
        if r["units_off_palette"]:
            note.append(f"off-palette={r['units_off_palette']}")
        if r["detachment_off_palette"]:
            note.append(f"det-off-palette={r['detachment_off_palette']}")
            agg["detachment off palette"] += 1
        if r["clamped_over_cap"]:
            note.append(f"cap-clamped={r['clamped_over_cap']}")
            agg["over-cap (clamped)"] += 1
        if r["clamped_over_limit"]:
            note.append(f"limit-clamped={r['clamped_over_limit']}")
            agg["over-limit (clamped)"] += 1
        if r["fill"] < 0.9:
            note.append("under-filled")
            agg["under-filled <90%"] += 1
        for i in r["issues"]:
            agg[i] += 1
        print(
            f"{r['faction']:28} {'yes' if r['legal'] else ' NO':>3} {r['points']:5} "
            f"{r['fill']*100:4.0f}% {r['theme_share']*100:4.0f}% {'Y' if r['warlord'] else 'N':>3} "
            f"{'; '.join(note)}"
        )

    print("\nGap tally (issue → factions):")
    for k, v in agg.most_common():
        print(f"  {k:28} {v}")


if __name__ == "__main__":
    main()

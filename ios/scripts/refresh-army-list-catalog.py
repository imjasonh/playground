#!/usr/bin/env python3
"""Refresh Army List catalog.json from BSData MFM + BattleScribe catalogues.

Requires network access to github.com. Wahapedia is optional and not used here —
BSData already scrapes the Munitorum Field Manual.

Usage:
  python3 ios/scripts/refresh-army-list-catalog.py
"""

from __future__ import annotations

import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unicodedata

try:
    import yaml
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "pyyaml", "-q"])
    import yaml

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "ios/Sources/Experiments/ArmyList/Catalog/Resources/catalog.json"


def slugify(name: str) -> str:
    n = unicodedata.normalize("NFKD", name)
    n = "".join(c for c in n if not unicodedata.combining(c))
    n = n.lower().replace("&", " and ")
    n = re.sub(r"[^a-z0-9]+", "-", n)
    return n.strip("-")


KEYWORD_KEEP = {
    "Battleline",
    "Character",
    "Epic Hero",
    "Infantry",
    "Vehicle",
    "Mounted",
    "Dedicated Transport",
    "Transport",
    "Fly",
    "Leader",
    "Psyker",
    "Grenades",
}


def clone(repo: str, dest: pathlib.Path) -> None:
    if dest.exists():
        shutil.rmtree(dest)
    subprocess.check_call(
        ["git", "clone", "--depth", "1", f"https://github.com/BSData/{repo}.git", str(dest)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def points_tiers(pricing):
    tiers = []
    for entry in pricing:
        match = re.match(r"\[(\d+),(\d*)\)?", entry["range"])
        if not match:
            raise ValueError(entry["range"])
        start = int(match.group(1))
        end = int(match.group(2)) if match.group(2) else None
        tiers.append(
            {
                "fromCopy": start,
                "toCopy": end,
                "byModels": {str(c["models"]): c["points"] for c in entry["costs"]},
            }
        )
    return tiers


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = pathlib.Path(tmp)
        clone("wh40k-11e-mfm", tmp_path / "mfm")
        clone("wh40k-11e", tmp_path / "bs")

        mfm = yaml.safe_load((tmp_path / "mfm/data/leagues-of-votann.yaml").read_text())
        bs = json.loads((tmp_path / "bs/Leagues of Votann.json").read_text())["catalogue"]

        bs_by_name = {}
        for entry in bs["sharedSelectionEntries"]:
            if entry.get("type") not in ("unit", "model") or not entry.get("name"):
                continue
            cats = [c.get("name") for c in entry.get("categoryLinks") or []]
            if any(c and str(c).startswith("Faction:") for c in cats):
                bs_by_name[entry["name"]] = entry

        def find_bs(name: str):
            if name in bs_by_name:
                return bs_by_name[name]
            target = slugify(name)
            for key, value in bs_by_name.items():
                if slugify(key) == target:
                    return value
            return None

        datasheets = []
        for unit in mfm["units"]:
            name = unit["name"]
            display = "Ûthar the Destined" if slugify(name).startswith("uthar") else name
            bs_entry = find_bs(name) or find_bs(display)
            keywords = []
            max_copies = None
            if bs_entry:
                for link in bs_entry.get("categoryLinks") or []:
                    label = link.get("name") or ""
                    if label in KEYWORD_KEEP or label.startswith("Faction:"):
                        keywords.append(label)
                for constraint in bs_entry.get("constraints") or []:
                    if (
                        constraint.get("field") == "selections"
                        and constraint.get("type") == "max"
                        and constraint.get("scope") == "force"
                    ):
                        max_copies = int(constraint["value"])
                        break
            if not keywords:
                keywords = ["Faction: Leagues of Votann"]

            sizes = sorted(
                {cost["models"] for tier in unit["pricing"] for cost in tier["costs"]}
            )
            role = None
            if "Leader" in keywords:
                role = "leader"
            elif "Character" in keywords:
                role = "character"

            datasheets.append(
                {
                    "id": slugify(display),
                    "name": display,
                    "factionID": "leagues-of-votann",
                    "keywords": keywords,
                    "characterRole": role,
                    "epicHero": "Epic Hero" in keywords,
                    "battleline": "Battleline" in keywords,
                    "dedicatedTransport": "Dedicated Transport" in keywords,
                    "minModels": min(sizes),
                    "maxModels": max(sizes),
                    "modelCounts": sizes,
                    "pointsTiers": points_tiers(unit["pricing"]),
                    "leaderTo": [slugify(x) for x in unit.get("leaderTo") or []],
                    "mustAttach": False,
                    "maxCopiesOverride": max_copies,
                }
            )

        force_map = {
            "DISRUPTION": "Disruption",
            "TAKE AND HOLD": "Take and Hold",
            "PURGE THE FOE": "Purge the Foe",
            "RECONNAISSANCE": "Reconnaissance",
            "PRIORITY ASSETS": "Priority Assets",
        }
        detachments = []
        for detachment in mfm["detachments"]:
            enhancements = []
            for enhancement in detachment.get("enhancements") or []:
                is_upgrade = "Upgrade" in enhancement["name"]
                clean = enhancement["name"].replace(" (Upgrade)", "").strip()
                enhancements.append(
                    {
                        "id": f"{slugify(detachment['name'])}--{slugify(clean)}",
                        "name": clean,
                        "points": enhancement["points"],
                        "isUpgrade": is_upgrade,
                    }
                )
            raw_force = (detachment.get("objectives") or ["Unknown"])[0]
            detachments.append(
                {
                    "id": slugify(detachment["name"]),
                    "name": detachment["name"],
                    "factionID": "leagues-of-votann",
                    "detachmentPoints": detachment["dp"],
                    "forceDisposition": force_map.get(raw_force.upper(), raw_force.title()),
                    "uniqueTag": detachment.get("unique"),
                    "enhancements": enhancements,
                }
            )

        catalog = {
            "version": f"11e-mfm-{mfm.get('version', 'unknown')}",
            "edition": "11th",
            "source": {
                "mfm": "https://github.com/BSData/wh40k-11e-mfm (data/leagues-of-votann.yaml)",
                "datasheetKeywords": "https://github.com/BSData/wh40k-11e (Leagues of Votann.json)",
                "mfmVersion": mfm.get("version"),
                "mfmFirstSeen": str(mfm.get("firstSeen")),
                "note": "Construction data only (points, DP, join edges, keywords). No ability prose.",
            },
            "battleSizes": [
                {
                    "id": "incursion",
                    "name": "Incursion",
                    "pointsLimit": 1000,
                    "detachmentPointsBudget": 2,
                    "enhancementPickLimit": 2,
                    "datasheetDuplicateLimit": 2,
                    "battlelineDuplicateLimit": 4,
                    "dedicatedTransportDuplicateLimit": 4,
                },
                {
                    "id": "strike-force",
                    "name": "Strike Force",
                    "pointsLimit": 2000,
                    "detachmentPointsBudget": 3,
                    "enhancementPickLimit": 4,
                    "datasheetDuplicateLimit": 3,
                    "battlelineDuplicateLimit": 6,
                    "dedicatedTransportDuplicateLimit": 6,
                },
            ],
            "factions": [
                {
                    "id": "leagues-of-votann",
                    "name": "Leagues of Votann",
                    "keywords": ["Faction: Leagues of Votann"],
                }
            ],
            "detachments": detachments,
            "datasheets": datasheets,
        }

        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(catalog, indent=2, ensure_ascii=False) + "\n")
        print(f"Wrote {OUT} ({len(detachments)} detachments, {len(datasheets)} datasheets)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

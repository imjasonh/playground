#!/usr/bin/env python3
"""Refresh Army List catalog.json from BSData MFM + BattleScribe catalogues.

Builds every faction present in wh40k-11e-mfm (Munitorum Field Manual scrape),
with datasheet keywords from wh40k-11e BattleScribe JSON where available.

Ids are namespaced as `{factionSlug}--{itemSlug}` so datasheets and detachments
do not collide across armies.

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

# MFM slug -> BattleScribe catalogue JSON filename(s) for keyword lookup.
BS_FILES_BY_SLUG: dict[str, list[str]] = {
    "adepta-sororitas": ["Imperium - Adepta Sororitas.json"],
    "adeptus-custodes": ["Imperium - Adeptus Custodes.json"],
    "adeptus-mechanicus": ["Imperium - Adeptus Mechanicus.json"],
    "aeldari": ["Aeldari - Craftworlds.json", "Aeldari - Aeldari Library.json"],
    "astra-militarum": [
        "Imperium - Astra Militarum.json",
        "Imperium - Astra Militarum - Library.json",
    ],
    "black-templars": ["Imperium - Black Templars.json", "Imperium - Space Marines.json"],
    "blood-angels": ["Imperium - Blood Angels.json", "Imperium - Space Marines.json"],
    "chaos-daemons": [
        "Chaos - Chaos Daemons.json",
        "Chaos - Chaos Daemons Library.json",
    ],
    "chaos-knights": [
        "Chaos - Chaos Knights.json",
        "Chaos - Chaos Knights Library.json",
    ],
    "chaos-space-marines": ["Chaos - Chaos Space Marines.json"],
    "chaos-titan-legions": ["Chaos - Titanicus Traitoris.json", "Library - Titans.json"],
    "dark-angels": ["Imperium - Dark Angels.json", "Imperium - Space Marines.json"],
    "death-guard": ["Chaos - Death Guard.json"],
    "deathwatch": ["Imperium - Deathwatch.json", "Imperium - Space Marines.json"],
    "drukhari": ["Aeldari - Drukhari.json", "Aeldari - Aeldari Library.json"],
    "emperors-children": ["Chaos - Emperor's Children.json"],
    "genestealer-cults": ["Genestealer Cults.json"],
    "grey-knights": ["Imperium - Grey Knights.json"],
    "imperial-agents": ["Imperium - Agents of the Imperium.json"],
    "imperial-knights": [
        "Imperium - Imperial Knights.json",
        "Imperium - Imperial Knights - Library.json",
    ],
    "leagues-of-votann": ["Leagues of Votann.json"],
    "necrons": ["Necrons.json"],
    "orks": ["Orks.json"],
    "space-marines": ["Imperium - Space Marines.json"],
    "space-wolves": ["Imperium - Space Wolves.json", "Imperium - Space Marines.json"],
    "tau-empire": ["T'au Empire.json"],
    "thousand-sons": ["Chaos - Thousand Sons.json"],
    "titan-legions": ["Imperium - Adeptus Titanicus.json", "Library - Titans.json"],
    "tyranids": ["Tyranids.json", "Library - Tyranids.json"],
    "world-eaters": ["Chaos - World Eaters.json"],
}

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

FORCE_MAP = {
    "DISRUPTION": "Disruption",
    "TAKE AND HOLD": "Take and Hold",
    "PURGE THE FOE": "Purge the Foe",
    "RECONNAISSANCE": "Reconnaissance",
    "PRIORITY ASSETS": "Priority Assets",
}


def slugify(name: str) -> str:
    n = unicodedata.normalize("NFKD", name)
    n = "".join(c for c in n if not unicodedata.combining(c))
    n = n.lower().replace("&", " and ")
    n = re.sub(r"[^a-z0-9]+", "-", n)
    return n.strip("-")


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
        by_models = {}
        for cost in entry["costs"]:
            models = cost.get("models")
            points = cost.get("points")
            if models is None or points is None:
                continue
            by_models[str(int(models))] = int(points)
        if not by_models:
            continue
        tiers.append(
            {
                "fromCopy": start,
                "toCopy": end,
                "byModels": by_models,
            }
        )
    return tiers


def load_bs_index(bs_dir: pathlib.Path, filenames: list[str]) -> dict[str, dict]:
    """Map unit/model display name -> sharedSelectionEntry (first wins)."""
    index: dict[str, dict] = {}
    for filename in filenames:
        path = bs_dir / filename
        if not path.exists():
            print(f"  warn: missing BS file {filename}", file=sys.stderr)
            continue
        catalogue = json.loads(path.read_text()).get("catalogue") or {}
        for entry in catalogue.get("sharedSelectionEntries") or []:
            if entry.get("type") not in ("unit", "model") or not entry.get("name"):
                continue
            name = entry["name"]
            index.setdefault(name, entry)
            index.setdefault(slugify(name), entry)
    return index


def find_bs(index: dict[str, dict], name: str):
    if name in index:
        return index[name]
    key = slugify(name)
    if key in index:
        return index[key]
    # Accent / punctuation tolerant scan.
    for candidate, entry in index.items():
        if isinstance(candidate, str) and slugify(candidate) == key:
            return entry
    return None


def extract_keywords(entry: dict | None, faction_name: str) -> list[str]:
    keywords: list[str] = []
    if entry:
        for link in entry.get("categoryLinks") or []:
            label = link.get("name") or ""
            if label in KEYWORD_KEEP or label.startswith("Faction:"):
                if label not in keywords:
                    keywords.append(label)
    faction_kw = f"Faction: {faction_name}"
    if faction_kw not in keywords:
        keywords.insert(0, faction_kw)
    return keywords


def max_copies_override(entry: dict | None) -> int | None:
    if not entry:
        return None
    for constraint in entry.get("constraints") or []:
        if (
            constraint.get("field") == "selections"
            and constraint.get("type") == "max"
            and constraint.get("scope") == "force"
        ):
            try:
                return int(constraint["value"])
            except (TypeError, ValueError):
                return None
    return None


def build_faction(mfm: dict, bs_index: dict[str, dict]) -> tuple[dict, list[dict], list[dict]]:
    faction_slug = mfm["slug"]
    faction_name = mfm["name"]
    faction = {
        "id": faction_slug,
        "name": faction_name,
        "keywords": [f"Faction: {faction_name}"],
    }

    # Local name/slug -> namespaced datasheet id (for leaderTo resolution).
    # Prefer the first occurrence when a name appears twice (Imperial Agents
    # reprints the same datasheet under different group titles).
    local_to_id: dict[str, str] = {}
    pending_units = []
    used_slugs: set[str] = set()
    for unit in mfm.get("units") or []:
        name = unit["name"]
        display = name
        unit_slug = slugify(display)
        # Keep Ûthar spelling when present.
        if unit_slug.startswith("uthar"):
            display = "Ûthar the Destined"
            unit_slug = "uthar-the-destined"
        group_title = (unit.get("groupTitle") or "").strip()
        if group_title and unit_slug in used_slugs:
            # Same datasheet name, different MFM pricing table — keep both.
            group_slug = slugify(group_title)
            unit_slug = f"{unit_slug}--{group_slug}"
            display = f"{display} ({group_title})"
        elif unit_slug in used_slugs:
            n = 2
            while f"{unit_slug}-{n}" in used_slugs:
                n += 1
            unit_slug = f"{unit_slug}-{n}"
            display = f"{display} ({n})"
        used_slugs.add(unit_slug)
        ds_id = f"{faction_slug}--{unit_slug}"
        # leaderTo resolves by bare name to the first datasheet of that name.
        local_to_id.setdefault(slugify(name), ds_id)
        local_to_id.setdefault(name.lower(), ds_id)
        local_to_id[unit_slug] = ds_id
        pending_units.append((unit, display, unit_slug, ds_id))

    datasheets = []
    skipped = 0
    for unit, display, unit_slug, ds_id in pending_units:
        tiers = points_tiers(unit.get("pricing") or [])
        if not tiers:
            skipped += 1
            continue
        sizes = sorted({int(k) for tier in tiers for k in tier["byModels"]})
        if not sizes:
            skipped += 1
            continue
        bs_entry = find_bs(bs_index, unit["name"]) or find_bs(bs_index, display)
        keywords = extract_keywords(bs_entry, faction_name)
        # MFM join edges imply Leader; keep Character/Leader even when BS miss.
        if unit.get("leaderTo"):
            if "Character" not in keywords:
                keywords.append("Character")
            if "Leader" not in keywords:
                keywords.append("Leader")
        # Name heuristics for common HQ datasheets that BS sometimes omits.
        name_l = unit["name"].lower()
        if len(keywords) <= 1 and any(
            tip in name_l
            for tip in (
                "captain",
                "lieutenant",
                "chaos lord",
                "brother-captain",
                "warlord titan",
            )
        ):
            if "Character" not in keywords:
                keywords.append("Character")
        role = None
        if "Leader" in keywords:
            role = "leader"
        elif "Character" in keywords:
            role = "character"
        leader_to = []
        for target in unit.get("leaderTo") or []:
            target_id = local_to_id.get(slugify(target)) or local_to_id.get(target.lower())
            if target_id:
                leader_to.append(target_id)
        datasheets.append(
            {
                "id": ds_id,
                "name": display,
                "factionID": faction_slug,
                "keywords": keywords,
                "characterRole": role,
                "epicHero": "Epic Hero" in keywords,
                "battleline": "Battleline" in keywords,
                "dedicatedTransport": "Dedicated Transport" in keywords,
                "minModels": min(sizes),
                "maxModels": max(sizes),
                "modelCounts": sizes,
                "pointsTiers": tiers,
                "leaderTo": leader_to,
                "mustAttach": False,
                "maxCopiesOverride": max_copies_override(bs_entry),
            }
        )

    detachments = []
    for detachment in mfm.get("detachments") or []:
        det_slug = slugify(detachment["name"])
        det_id = f"{faction_slug}--{det_slug}"
        enhancements = []
        for enhancement in detachment.get("enhancements") or []:
            is_upgrade = "Upgrade" in enhancement["name"]
            clean = enhancement["name"].replace(" (Upgrade)", "").strip()
            enhancements.append(
                {
                    "id": f"{det_id}--{slugify(clean)}",
                    "name": clean,
                    "points": int(enhancement["points"]),
                    "isUpgrade": is_upgrade,
                }
            )
        raw_force = (detachment.get("objectives") or ["Unknown"])[0]
        detachments.append(
            {
                "id": det_id,
                "name": detachment["name"],
                "factionID": faction_slug,
                "detachmentPoints": int(detachment["dp"]),
                "forceDisposition": FORCE_MAP.get(str(raw_force).upper(), str(raw_force).title()),
                "uniqueTag": detachment.get("unique"),
                "enhancements": enhancements,
            }
        )

    if skipped:
        print(f"  {faction_slug}: skipped {skipped} units without points tiers", file=sys.stderr)
    return faction, detachments, datasheets


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = pathlib.Path(tmp)
        print("Cloning BSData catalogues…")
        clone("wh40k-11e-mfm", tmp_path / "mfm")
        clone("wh40k-11e", tmp_path / "bs")

        data_dir = tmp_path / "mfm/data"
        meta = {}
        meta_path = data_dir / "meta.yaml"
        if meta_path.exists():
            meta = yaml.safe_load(meta_path.read_text()) or {}

        factions: list[dict] = []
        detachments: list[dict] = []
        datasheets: list[dict] = []
        mfm_versions: list[str] = []

        yaml_paths = sorted(
            p for p in data_dir.glob("*.yaml") if p.name != "meta.yaml"
        )
        for path in yaml_paths:
            mfm = yaml.safe_load(path.read_text())
            if not mfm or "slug" not in mfm:
                print(f"  skip {path.name}: missing slug", file=sys.stderr)
                continue
            slug = mfm["slug"]
            if slug not in BS_FILES_BY_SLUG:
                print(f"  warn: no BS mapping for {slug}; keywords will be faction-only", file=sys.stderr)
            bs_index = load_bs_index(tmp_path / "bs", BS_FILES_BY_SLUG.get(slug, []))
            faction, dets, sheets = build_faction(mfm, bs_index)
            factions.append(faction)
            detachments.extend(dets)
            datasheets.extend(sheets)
            if mfm.get("version"):
                mfm_versions.append(str(mfm["version"]))
            print(
                f"  {faction['name']}: {len(sheets)} datasheets, {len(dets)} detachments"
            )

        factions.sort(key=lambda f: f["name"].casefold())
        detachments.sort(key=lambda d: (d["factionID"], d["name"].casefold()))
        datasheets.sort(key=lambda d: (d["factionID"], d["name"].casefold()))

        version_label = meta.get("version") or (
            f"multi-{max(mfm_versions)}" if mfm_versions else "unknown"
        )
        catalog = {
            "version": f"11e-mfm-{version_label}",
            "edition": "11th",
            "source": {
                "mfm": "https://github.com/BSData/wh40k-11e-mfm (data/*.yaml)",
                "datasheetKeywords": "https://github.com/BSData/wh40k-11e (*.json)",
                "mfmVersion": str(version_label),
                "mfmFirstSeen": str(meta.get("generatedAt") or meta.get("date") or ""),
                "note": "Construction data for all MFM factions. Ids are faction-prefixed. No ability prose.",
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
            "factions": factions,
            "detachments": detachments,
            "datasheets": datasheets,
        }

        # Sanity: unique ids
        for label, items in (
            ("faction", factions),
            ("detachment", detachments),
            ("datasheet", datasheets),
        ):
            ids = [i["id"] for i in items]
            if len(ids) != len(set(ids)):
                raise SystemExit(f"Duplicate {label} ids detected")

        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(catalog, indent=2, ensure_ascii=False) + "\n")
        print(
            f"Wrote {OUT} ({len(factions)} factions, {len(detachments)} detachments, {len(datasheets)} datasheets)"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

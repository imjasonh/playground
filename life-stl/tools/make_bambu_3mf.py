#!/usr/bin/env python3
"""Build a Bambu Studio project .3mf from a binary STL plus print settings.

The output embeds a full flattened settings dump (printer + process +
filament) the way Bambu Studio's own project files do, so opening the .3mf
loads both the geometry and the intended print settings. Profiles are
flattened from the official Bambu Studio profile library (its ``resources/
profiles/BBL`` directory), with model-specific overrides applied on top and
recorded in ``different_settings_to_system`` so the UI shows them as
modifications of the system presets.

Usage:
  python3 make_bambu_3mf.py \
      --stl ../examples/gusset-acorn.stl \
      --profiles /path/to/BambuStudio/resources/profiles/BBL \
      --printer "Bambu Lab A1 mini 0.4 nozzle" \
      --process "0.20mm Standard @BBL A1M" \
      --filament "Generic PLA @BBL A1M" \
      --override key=value --override key=value \
      --bed-size 180 \
      -o ../examples/gusset-acorn-a1mini.3mf

Only Python 3 stdlib is required. Geometry is centered on the bed.
"""

import argparse
import json
import struct
import sys
import zipfile
from pathlib import Path
from xml.sax.saxutils import escape

# Version stamp Bambu Studio checks for compatibility. Keep this at 02.x so
# BambuStudio 2.x loads the file on its current (non-legacy) code path.
APP_VERSION = "02.05.00.00"


def load_profile_tree(profiles_dir: Path):
    """Map profile name → parsed JSON for every profile under BBL/."""
    by_name = {}
    for sub in ("machine", "process", "filament"):
        for path in (profiles_dir / sub).glob("*.json"):
            try:
                data = json.loads(path.read_text())
            except json.JSONDecodeError:
                continue
            name = data.get("name")
            if name:
                by_name[name] = data
    return by_name


META_KEYS = {
    "type", "name", "inherits", "from", "setting_id", "instantiation",
    "description", "filament_id", "info_file", "renamed_from", "upward_compatible_machine",
}


def flatten(by_name, name):
    """Resolve an ``inherits`` chain, child values overriding parents."""
    chain = []
    cur = name
    seen = set()
    while cur:
        if cur in seen:
            raise SystemExit(f"inheritance loop at {cur!r}")
        seen.add(cur)
        node = by_name.get(cur)
        if node is None:
            raise SystemExit(f"profile not found: {cur!r} (searched {len(by_name)} profiles)")
        chain.append(node)
        cur = node.get("inherits")
    merged = {}
    for node in reversed(chain):
        for k, v in node.items():
            if k not in META_KEYS:
                merged[k] = v
    return merged


def read_binary_stl(path: Path):
    """Return (vertices, triangles) with deduplicated vertices."""
    data = path.read_bytes()
    (count,) = struct.unpack_from("<I", data, 80)
    verts = []
    index = {}
    tris = []
    off = 84
    for _ in range(count):
        # Skip the 12-byte normal; slicers recompute normals anyway.
        tri = []
        for v in range(3):
            x, y, z = struct.unpack_from("<3f", data, off + 12 + v * 12)
            key = (round(x, 4), round(y, 4), round(z, 4))
            i = index.get(key)
            if i is None:
                i = len(verts)
                index[key] = i
                verts.append(key)
            tri.append(i)
        tris.append(tuple(tri))
        off += 50
    return verts, tris


def model_xml(verts, tris, bed_size_mm: float):
    """Standard 3MF model part with the mesh centered on the bed.

    BambuStudio 2.x expects a two-level object structure:
      - Object 1 (parent): build item, holds a <components> reference.
      - Object 2 (child):  the actual mesh geometry.
    model_settings.config then uses <part id="2"> to reference the mesh.
    """
    min_x = min(v[0] for v in verts)
    max_x = max(v[0] for v in verts)
    min_y = min(v[1] for v in verts)
    max_y = max(v[1] for v in verts)
    min_z = min(v[2] for v in verts)
    tx = bed_size_mm / 2.0 - (min_x + max_x) / 2.0
    ty = bed_size_mm / 2.0 - (min_y + max_y) / 2.0
    tz = -min_z
    transform = f"1 0 0 0 1 0 0 0 1 {tx:.3f} {ty:.3f} {tz:.3f}"

    out = []
    out.append('<?xml version="1.0" encoding="UTF-8"?>')
    out.append(
        '<model unit="millimeter" xml:lang="en-US" '
        'xmlns="http://schemas.microsoft.com/3dmanufacturing/core/2015/02" '
        'xmlns:BambuStudio="http://schemas.bambulab.com/package/2021">'
    )
    out.append(f'<metadata name="Application">BambuStudio-{APP_VERSION}</metadata>')
    out.append('<metadata name="BambuStudio:3mfVersion">2</metadata>')
    out.append("<resources>")
    # Parent object: no mesh, just a component reference to the child.
    out.append('<object id="1" type="model">')
    out.append("<components>")
    out.append('<component objectid="2" transform="1 0 0 0 1 0 0 0 1 0 0 0"/>')
    out.append("</components>")
    out.append("</object>")
    # Child object: the actual mesh geometry.
    out.append('<object id="2" type="model">')
    out.append("<mesh>")
    out.append("<vertices>")
    for x, y, z in verts:
        out.append(f'<vertex x="{x:g}" y="{y:g}" z="{z:g}"/>')
    out.append("</vertices>")
    out.append("<triangles>")
    for a, b, c in tris:
        out.append(f'<triangle v1="{a}" v2="{b}" v3="{c}"/>')
    out.append("</triangles>")
    out.append("</mesh>")
    out.append("</object>")
    out.append("</resources>")
    out.append("<build>")
    out.append(f'<item objectid="1" transform="{transform}" printable="1"/>')
    out.append("</build>")
    out.append("</model>")
    return "\n".join(out)


def model_settings_xml(name: str):
    # part id="2" references the child mesh object (id=2 in 3dmodel.model).
    name = escape(name, {'"': "&quot;"})
    return f"""<?xml version="1.0" encoding="UTF-8"?>
<config>
  <object id="1">
    <metadata key="name" value="{name}"/>
    <metadata key="extruder" value="1"/>
    <part id="2" subtype="normal_part">
      <metadata key="name" value="{name}"/>
    </part>
  </object>
  <plate>
    <metadata key="plater_id" value="1"/>
    <metadata key="plater_name" value=""/>
    <metadata key="locked" value="false"/>
    <model_instance>
      <metadata key="object_id" value="1"/>
      <metadata key="instance_id" value="0"/>
      <metadata key="identify_id" value="1"/>
    </model_instance>
  </plate>
</config>
"""


CONTENT_TYPES = """<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
 <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
 <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
 <Override PartName="/Metadata/project_settings.config" ContentType="application/json"/>
 <Override PartName="/Metadata/model_settings.config" ContentType="text/xml"/>
 <Override PartName="/Metadata/slice_info.config" ContentType="text/xml"/>
</Types>
"""

SLICE_INFO = """<?xml version="1.0" encoding="UTF-8"?>
<config/>
"""

RELS = """<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
 <Relationship Target="/3D/3dmodel.model" Id="rel-1" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--stl", required=True, type=Path)
    ap.add_argument("--profiles", required=True, type=Path,
                    help="BambuStudio resources/profiles/BBL directory")
    ap.add_argument("--printer", required=True)
    ap.add_argument("--process", required=True)
    ap.add_argument("--filament", required=True)
    ap.add_argument("--override", action="append", default=[],
                    metavar="KEY=VALUE", help="process-level setting override")
    ap.add_argument("--bed-type", default="Textured PEI Plate")
    ap.add_argument("--bed-size", type=float, default=180.0, help="bed edge (mm)")
    ap.add_argument("--name", default=None, help="object name (default: STL stem)")
    ap.add_argument("-o", "--output", required=True, type=Path)
    args = ap.parse_args()

    by_name = load_profile_tree(args.profiles)
    printer = flatten(by_name, args.printer)
    process = flatten(by_name, args.process)
    filament = flatten(by_name, args.filament)

    overrides = {}
    for item in args.override:
        key, _, value = item.partition("=")
        if not _:
            ap.error(f"--override needs KEY=VALUE, got {item!r}")
        overrides[key] = value

    # Project settings: flattened printer+filament+process, overrides on top,
    # plus the preset-binding metadata Bambu Studio expects.
    config = {}
    config.update(printer)
    config.update(filament)
    config.update(process)
    config.update(overrides)
    config.update({
        "name": "project_settings",
        "from": "project",
        "version": APP_VERSION,
        "is_custom_defined": "0",
        "curr_bed_type": args.bed_type,
        "print_settings_id": args.process,
        "printer_settings_id": args.printer,
        "filament_settings_id": [args.filament],
        "different_settings_to_system": [
            # Three slots: process overrides, filament overrides, printer overrides.
            # Semicolon-separated key names; empty string means "no overrides".
            ";".join(sorted(overrides)), "", "",
        ],
    })

    # BambuStudio 2.x crashes with a null-pointer dereference if
    # nozzle_volume_type is absent from the project config.  Older profile
    # libraries (pre-2.x) do not include it, so add a safe default here.
    if "nozzle_volume_type" not in config:
        # nozzle_diameter is a per-extruder array; fall back to 1 entry for
        # the common single-nozzle case when the key is also absent.
        nozzle_count = len(config.get("nozzle_diameter", ["0.4"]))
        config["nozzle_volume_type"] = ["Standard"] * nozzle_count

    verts, tris = read_binary_stl(args.stl)
    name = args.name or args.stl.stem
    print(f"{args.stl.name}: {len(verts)} vertices, {len(tris)} triangles")

    with zipfile.ZipFile(args.output, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml", CONTENT_TYPES)
        zf.writestr("_rels/.rels", RELS)
        zf.writestr("3D/3dmodel.model", model_xml(verts, tris, args.bed_size))
        zf.writestr("Metadata/model_settings.config", model_settings_xml(name))
        zf.writestr("Metadata/slice_info.config", SLICE_INFO)
        zf.writestr("Metadata/project_settings.config",
                     json.dumps(config, indent=4, sort_keys=True))
    size = args.output.stat().st_size
    print(f"wrote {args.output} ({size / 1e6:.1f} MB)")


if __name__ == "__main__":
    sys.exit(main())

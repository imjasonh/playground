#!/usr/bin/env python3
"""Place and route the board with Freerouting's Specctra DSN/SES flow.

The script builds the placed board from the committed schematic, exports a
Specctra DSN file, runs Freerouting, imports the resulting SES file, refills
the copper zones, and exports the fabrication files.

Set ``FREEROUTING_JAR`` to a Freerouting 2.4.1 JAR. Freerouting 2.4.1 requires
Java 25, so set ``FREEROUTING_JAVA`` when ``java`` does not select that
runtime. On headless Linux, install ``xvfb-run`` for Freerouting's AWT setup.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, "/usr/lib/python3/dist-packages")
import pcbnew  # noqa: E402

import generate_pcb  # noqa: E402
import layout_route  # noqa: E402

HERE = Path(__file__).resolve().parent
BOARD = HERE / "inkbot-magsafe.kicad_pcb"
SCHEMATIC = HERE / "inkbot-magsafe.kicad_sch"
NETLIST = layout_route.NETLIST
FAB = layout_route.FAB
DSN = FAB / "inkbot-magsafe.dsn"
SES = FAB / "inkbot-magsafe.ses"


def fill_zones(board: pcbnew.BOARD) -> None:
    """Fill every copper zone on the board."""
    copper_zones = pcbnew.ZONES()
    for zone in board.Zones():
        if not zone.GetIsRuleArea():
            copper_zones.append(zone)
    pcbnew.ZONE_FILLER(board).Fill(copper_zones)


def build_placed_board() -> pcbnew.BOARD:
    """Build the board outline, place footprints, assign nets, and add planes."""
    generate_pcb.main()
    subprocess.run(
        [
            "kicad-cli",
            "sch",
            "export",
            "netlist",
            "-o",
            str(NETLIST),
            str(SCHEMATIC),
        ],
        check=True,
    )

    components, nets = layout_route.parse_netlist(NETLIST)
    board = pcbnew.LoadBoard(str(BOARD))
    for footprint in list(board.GetFootprints()):
        board.Remove(footprint)

    netmap: dict[str, pcbnew.NETINFO_ITEM] = {}
    for name in list(nets) + [layout_route.GND, layout_route.VSYS]:
        if name not in netmap:
            net = pcbnew.NETINFO_ITEM(board, name)
            board.Add(net)
            netmap[name] = net

    placed: dict[str, pcbnew.FOOTPRINT] = {}
    for reference, library_name in components.items():
        if not library_name or reference not in layout_route.PLACEMENT:
            continue
        x, y, rotation = layout_route.PLACEMENT[reference]
        footprint = layout_route.load_fp(library_name)
        board.Add(footprint)
        footprint.SetReference(reference)
        footprint.SetPosition(pcbnew.VECTOR2I(layout_route.mm(x), layout_route.mm(y)))
        if rotation:
            footprint.SetOrientationDegrees(rotation)
        footprint.Flip(footprint.GetPosition(), False)
        footprint.Reference().SetLayer(pcbnew.B_Fab)
        footprint.Reference().SetVisible(True)
        placed[reference] = footprint

    def assign_pad(reference: str, pad_number: str, net_name: str) -> None:
        footprint = placed.get(reference)
        if footprint is None:
            return
        for pad in footprint.Pads():
            if pad.GetNumber() == pad_number:
                pad.SetNet(netmap[net_name])
                return

    for net_name, nodes in nets.items():
        if net_name.startswith("unconnected-"):
            continue
        for reference, pad_number in nodes:
            assign_pad(reference, pad_number, net_name)
    for pad_number in layout_route.MODULE_GND_PADS:
        assign_pad("U1", pad_number, layout_route.GND)

    def add_plane(layer: int, net_name: str) -> None:
        zone = pcbnew.ZONE(board)
        zone.SetLayer(layer)
        zone.SetNet(netmap[net_name])
        zone.SetLocalClearance(layout_route.mm(layout_route.CLEAR))
        zone.SetMinThickness(layout_route.mm(0.2))
        outline = pcbnew.SHAPE_POLY_SET()
        outline.NewOutline()
        for x, y in (
            (0.2, 0.2),
            (layout_route.BOARD_W - 0.2, 0.2),
            (layout_route.BOARD_W - 0.2, layout_route.BOARD_H - 0.2),
            (0.2, layout_route.BOARD_H - 0.2),
        ):
            outline.Append(layout_route.mm(x), layout_route.mm(y))
        zone.SetOutline(outline)
        board.Add(zone)

    add_plane(pcbnew.In2_Cu, layout_route.GND)
    add_plane(pcbnew.B_Cu, layout_route.GND)
    add_plane(pcbnew.F_Cu, layout_route.GND)
    add_plane(pcbnew.In1_Cu, layout_route.VSYS)

    antenna_keepout = pcbnew.ZONE(board)
    antenna_keepout.SetIsRuleArea(True)
    antenna_keepout.SetDoNotAllowCopperPour(True)
    antenna_keepout.SetDoNotAllowTracks(True)
    antenna_keepout.SetDoNotAllowVias(True)
    layers = pcbnew.LSET()
    for layer in (pcbnew.F_Cu, pcbnew.In1_Cu, pcbnew.In2_Cu, pcbnew.B_Cu):
        layers.AddLayer(layer)
    antenna_keepout.SetLayerSet(layers)
    outline = pcbnew.SHAPE_POLY_SET()
    outline.NewOutline()
    for x, y in ((1.5, 85), (11, 85), (11, 93), (1.5, 93)):
        outline.Append(layout_route.mm(x), layout_route.mm(y))
    antenna_keepout.SetOutline(outline)
    board.Add(antenna_keepout)

    board.BuildConnectivity()
    fill_zones(board)
    pcbnew.SaveBoard(str(BOARD), board)
    return board


def freerouting_command() -> list[str]:
    """Return the validated Freerouting command."""
    jar_value = os.environ.get("FREEROUTING_JAR")
    if not jar_value:
        raise SystemExit("set FREEROUTING_JAR to the Freerouting 2.4.1 JAR")
    jar = Path(jar_value).expanduser().resolve()
    if not jar.is_file():
        raise SystemExit(f"missing Freerouting JAR: {jar}")

    java = os.environ.get("FREEROUTING_JAVA", "java")
    if "/" in java:
        if not Path(java).is_file():
            raise SystemExit(f"missing Java runtime: {java}")
    elif shutil.which(java) is None:
        raise SystemExit(f"Java runtime not found: {java}")

    command = [
        java,
        "-jar",
        str(jar),
        "-de",
        str(DSN),
        "-do",
        str(SES),
        "-mp",
        os.environ.get("FREEROUTING_PASSES", "100"),
        "-mt",
        os.environ.get("FREEROUTING_THREADS", "2"),
        "-l",
        "en",
    ]
    if sys.platform.startswith("linux") and not os.environ.get("DISPLAY"):
        xvfb_run = shutil.which("xvfb-run")
        if xvfb_run is None:
            raise SystemExit("headless Linux requires xvfb-run")
        command = [xvfb_run, "-a", *command]
    return command


def main() -> None:
    FAB.mkdir(exist_ok=True)
    board = build_placed_board()
    if not pcbnew.ExportSpecctraDSN(board, str(DSN)):
        raise SystemExit(f"failed to export Specctra DSN: {DSN}")

    SES.unlink(missing_ok=True)
    command = freerouting_command()
    print("running:", " ".join(command))
    subprocess.run(
        command,
        check=True,
        timeout=int(os.environ.get("FREEROUTING_TIMEOUT", "3600")),
    )
    if not SES.is_file() or SES.stat().st_size == 0:
        raise SystemExit(f"Freerouting did not write a session: {SES}")

    if not pcbnew.ImportSpecctraSES(board, str(SES)):
        raise SystemExit(f"failed to import Specctra SES: {SES}")
    board.BuildConnectivity()
    fill_zones(board)
    board.BuildConnectivity()
    pcbnew.SaveBoard(str(BOARD), board)

    connectivity = board.GetConnectivity()
    unconnected = (
        connectivity.GetUnconnectedCount(True)
        if hasattr(connectivity, "GetUnconnectedCount")
        else -1
    )
    print(f"imported {SES}; open ratsnest connections: {unconnected}")
    layout_route.export_fab()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Place and route the EVT board with Freerouting's DSN/SES flow."""

from __future__ import annotations

import json
import math
import os
import re
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
VIA_NAME = re.compile(r"Via\[(\d+)-(\d+)\]_(\d+):(\d+)_um")


def fill_zones(board: pcbnew.BOARD) -> None:
    """Fill every copper zone on the board."""
    copper_zones = pcbnew.ZONES()
    for zone in board.Zones():
        if not zone.GetIsRuleArea():
            copper_zones.append(zone)
    pcbnew.ZONE_FILLER(board).Fill(copper_zones)


def parse_sexpression(text: str) -> list[object]:
    """Parse the subset of Specctra S-expressions used by SES files."""
    root: list[object] = []
    stack = [root]
    for match in re.finditer(r'\(|\)|"(?:\\.|[^"\\])*"|[^\s()]+', text):
        token = match.group(0)
        if token == "(":
            form: list[object] = []
            stack[-1].append(form)
            stack.append(form)
        elif token == ")":
            if len(stack) == 1:
                raise ValueError("unexpected closing parenthesis in SES file")
            stack.pop()
        elif token.startswith('"'):
            stack[-1].append(json.loads(token))
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ValueError("unterminated form in SES file")
    return root


def child_form(form: list[object], name: str) -> list[object]:
    """Return the first direct child form with the requested name."""
    for item in form[1:]:
        if isinstance(item, list) and item and item[0] == name:
            return item
    raise ValueError(f"missing ({name} ...) form in SES file")


def import_freerouting_session(board: pcbnew.BOARD, path: Path) -> None:
    """Import Freerouting wires and vias through the headless pcbnew API."""
    parsed = parse_sexpression(path.read_text())
    if len(parsed) != 1 or not isinstance(parsed[0], list):
        raise ValueError("SES file must contain one session form")
    session = parsed[0]
    if not session or session[0] != "session":
        raise ValueError("SES file does not start with a session form")

    routes = child_form(session, "routes")
    resolution = child_form(routes, "resolution")
    if len(resolution) != 3 or resolution[1] != "um":
        raise ValueError(f"unsupported SES resolution: {resolution}")
    nanometers_per_unit = 1000 / int(str(resolution[2]))
    network = child_form(routes, "network_out")
    copper_layers = [
        board.GetLayerID(name) for name in ("F.Cu", "In1.Cu", "In2.Cu", "B.Cu")
    ]

    def coordinate(value: object, invert: bool = False) -> int:
        result = round(float(str(value)) * nanometers_per_unit)
        return -result if invert else result

    for old_item in list(board.GetTracks()):
        if not old_item.IsLocked():
            board.Remove(old_item)

    wire_count = 0
    via_count = 0
    for net_form in network[1:]:
        if not isinstance(net_form, list) or len(net_form) < 2 or net_form[0] != "net":
            continue
        net_name = str(net_form[1])
        net = board.FindNet(net_name)
        if net is None or net.GetNetCode() == 0:
            raise ValueError(f"SES route refers to unknown net: {net_name}")

        for route_item in net_form[2:]:
            if not isinstance(route_item, list) or not route_item:
                continue
            if route_item[0] == "wire":
                if len(route_item) != 2 or not isinstance(route_item[1], list):
                    raise ValueError(f"malformed wire for net {net_name}")
                path_form = route_item[1]
                if len(path_form) < 7 or path_form[0] != "path":
                    raise ValueError(f"malformed path for net {net_name}")
                layer = board.GetLayerID(str(path_form[1]))
                if layer not in (pcbnew.F_Cu, pcbnew.B_Cu):
                    raise ValueError(f"signal route on reserved plane for net {net_name}")
                width = max(
                    coordinate(path_form[2]),
                    layout_route.POWER_WIDTHS.get(net_name, layout_route.mm(0.15)),
                )
                values = path_form[3:]
                if len(values) % 2:
                    raise ValueError(f"odd coordinate count for net {net_name}")
                points = [
                    pcbnew.VECTOR2I(
                        coordinate(values[index]),
                        coordinate(values[index + 1], True),
                    )
                    for index in range(0, len(values), 2)
                ]
                for start, end in zip(points, points[1:]):
                    if start == end:
                        continue
                    track = pcbnew.PCB_TRACK(board)
                    track.SetStart(start)
                    track.SetEnd(end)
                    track.SetWidth(width)
                    track.SetLayer(layer)
                    track.SetNet(net)
                    board.Add(track)
                    wire_count += 1
            elif route_item[0] == "via":
                if len(route_item) < 4:
                    raise ValueError(f"malformed via for net {net_name}")
                match = VIA_NAME.fullmatch(str(route_item[1]))
                if match is None:
                    raise ValueError(f"unsupported via padstack: {route_item[1]}")
                start_layer, end_layer, diameter_um, drill_um = map(int, match.groups())
                if not 0 <= start_layer < len(copper_layers) or not 0 <= end_layer < len(
                    copper_layers
                ):
                    raise ValueError(f"via layer outside board stack: {route_item[1]}")
                via = pcbnew.PCB_VIA(board)
                via.SetPosition(
                    pcbnew.VECTOR2I(
                        coordinate(route_item[2]),
                        coordinate(route_item[3], True),
                    )
                )
                via.SetWidth(max(diameter_um * 1000, layout_route.VIA_D))
                via.SetDrill(max(drill_um * 1000, layout_route.VIA_DRILL))
                via.SetLayerPair(copper_layers[start_layer], copper_layers[end_layer])
                via.SetNet(net)
                board.Add(via)
                via_count += 1
    print(f"imported {wire_count} track segments and {via_count} vias")


def add_rect_rule_area(
    board: pcbnew.BOARD,
    points: list[tuple[float, float]],
    layers: pcbnew.LSET,
    keepalive: list[pcbnew.SHAPE_POLY_SET],
) -> pcbnew.ZONE:
    """Add a copper, track, and via keep-out polygon."""
    zone = pcbnew.ZONE(board)
    zone.SetIsRuleArea(True)
    zone.SetDoNotAllowCopperPour(True)
    zone.SetDoNotAllowTracks(True)
    zone.SetDoNotAllowVias(True)
    zone.SetLayerSet(layers)
    outline = pcbnew.SHAPE_POLY_SET()
    outline.NewOutline()
    for x, y in points:
        outline.Append(layout_route.mm(x), layout_route.mm(y))
    zone.SetOutline(outline)
    keepalive.append(outline)
    board.Add(zone)
    return zone


def build_placed_board() -> tuple[pcbnew.BOARD, list[pcbnew.SHAPE_POLY_SET]]:
    """Build the outline, place footprints, assign nets, and add power planes."""
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
    for name in nets:
        net = pcbnew.NETINFO_ITEM(board, name)
        board.Add(net)
        netmap[name] = net

    placed: dict[str, pcbnew.FOOTPRINT] = {}
    expected = {
        reference
        for reference, footprint in components.items()
        if footprint and reference in layout_route.PLACEMENT
    }
    if expected != set(layout_route.PLACEMENT):
        extra = sorted(set(layout_route.PLACEMENT) - expected)
        missing = sorted(expected - set(layout_route.PLACEMENT))
        raise ValueError(f"placement mismatch; extra={extra}, missing={missing}")

    for reference in sorted(expected):
        library_name = components[reference]
        x, y, rotation = layout_route.PLACEMENT[reference]
        footprint = layout_route.load_fp(library_name)
        board.Add(footprint)
        footprint.SetReference(reference)
        footprint.SetPosition(pcbnew.VECTOR2I(layout_route.mm(x), layout_route.mm(y)))
        if rotation:
            footprint.SetOrientationDegrees(rotation)
        footprint.Flip(footprint.GetPosition(), False)
        for graphic in footprint.GraphicalItems():
            if graphic.GetLayer() == pcbnew.B_SilkS:
                graphic.SetLayer(pcbnew.B_Fab)
        footprint.Reference().SetLayer(pcbnew.B_Fab)
        footprint.Reference().SetVisible(True)
        placed[reference] = footprint

    assigned: set[tuple[str, str]] = set()
    intentional_nc = {
        node
        for net_name, nodes in nets.items()
        if net_name.startswith("unconnected-")
        for node in nodes
    }
    for net_name, nodes in nets.items():
        if net_name.startswith("unconnected-"):
            continue
        for reference, pad_number in nodes:
            footprint = placed.get(reference)
            if footprint is None:
                continue
            found = False
            for pad in footprint.Pads():
                if pad.GetNumber() == pad_number:
                    pad.SetNet(netmap[net_name])
                    if net_name == layout_route.GND and reference in {
                        "U1",
                        "U2",
                        "U3",
                        "U4",
                    }:
                        pad.SetZoneConnection(pcbnew.ZONE_CONNECTION_FULL)
                    found = True
            if not found:
                raise ValueError(f"missing pad {reference}.{pad_number}")
            assigned.add((reference, pad_number))

    for reference, footprint in placed.items():
        for pad in footprint.Pads():
            key = (reference, pad.GetNumber())
            if not pad.GetNumber() or key in assigned or key in intentional_nc:
                continue
            if pad.GetNumber() == "MP":
                pad.SetNet(netmap[layout_route.GND])
                continue
            raise ValueError(f"unassigned board pad {reference}.{pad.GetNumber()}")

    settings = board.GetDesignSettings()
    settings.SetCustomTrackWidth(layout_route.TRACK_W)
    settings.SetCustomViaSize(layout_route.VIA_D)
    settings.SetCustomViaDrill(layout_route.VIA_DRILL)
    settings.m_ViasDimensionsList.clear()
    settings.m_ViasDimensionsList.append(
        pcbnew.VIA_DIMENSION(layout_route.VIA_D, layout_route.VIA_DRILL)
    )
    settings.SetViaSizeIndex(0)
    keepalive: list[pcbnew.SHAPE_POLY_SET] = []

    def add_plane(layer: int, net_name: str, pad_connection: int) -> None:
        zone = pcbnew.ZONE(board)
        zone.SetLayer(layer)
        zone.SetNet(netmap[net_name])
        zone.SetLocalClearance(layout_route.mm(layout_route.CLEAR))
        zone.SetMinThickness(layout_route.mm(0.2))
        zone.SetPadConnection(pad_connection)
        outline = pcbnew.SHAPE_POLY_SET()
        outline.NewOutline()
        for x, y in (
            (0.5, 0.5),
            (layout_route.BOARD_W - 0.5, 0.5),
            (layout_route.BOARD_W - 0.5, layout_route.BOARD_H - 0.5),
            (0.5, layout_route.BOARD_H - 0.5),
        ):
            outline.Append(layout_route.mm(x), layout_route.mm(y))
        zone.SetOutline(outline)
        keepalive.append(outline)
        board.Add(zone)

    add_plane(pcbnew.In1_Cu, layout_route.SYS, pcbnew.ZONE_CONNECTION_FULL)
    add_plane(pcbnew.In2_Cu, layout_route.GND, pcbnew.ZONE_CONNECTION_FULL)
    add_plane(pcbnew.F_Cu, layout_route.GND, pcbnew.ZONE_CONNECTION_THERMAL)
    add_plane(pcbnew.B_Cu, layout_route.GND, pcbnew.ZONE_CONNECTION_THERMAL)

    all_layers = pcbnew.LSET()
    for layer in (pcbnew.F_Cu, pcbnew.In1_Cu, pcbnew.In2_Cu, pcbnew.B_Cu):
        all_layers.AddLayer(layer)

    # Keep every copper layer out of the magnetic assembly and receiver-coil
    # area. The receiver coil connects through its flexible lead to J3.
    circle = [
        (
            layout_route.RING_CX
            + layout_route.RING_RADIUS * math.cos(2 * math.pi * index / 48),
            layout_route.RING_CY
            + layout_route.RING_RADIUS * math.sin(2 * math.pi * index / 48),
        )
        for index in range(48)
    ]
    add_rect_rule_area(board, circle, all_layers, keepalive)

    # The board cutout already removes FR-4. This larger rule area prevents
    # copper and vias from violating routed-edge clearance.
    add_rect_rule_area(
        board,
        [(12.5, 58.0), (47.5, 58.0), (47.5, 82.0), (12.5, 82.0)],
        all_layers,
        keepalive,
    )

    # The Raytac footprint includes an antenna keep-out. This explicit area
    # also protects it if a future library revision drops the footprint rule.
    add_rect_rule_area(
        board,
        [(0.0, 83.0), (4.25, 83.0), (4.25, 95.0), (0.0, 95.0)],
        all_layers,
        keepalive,
    )

    board.BuildConnectivity()
    fill_zones(board)
    pcbnew.SaveBoard(str(BOARD), board)
    return board, keepalive


def mark_power_layers(path: Path) -> None:
    """Mark the SYS and GND planes as non-routable in the DSN export."""
    text = path.read_text()
    for layer in ("In1.Cu", "In2.Cu"):
        signal = f"    (layer {layer}\n      (type signal)"
        power = f"    (layer {layer}\n      (type power)"
        if text.count(signal) != 1:
            raise ValueError(f"cannot find {layer} in {path}")
        text = text.replace(signal, power)
    path.write_text(text)


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
        os.environ.get("FREEROUTING_PASSES", "150"),
        "-mt",
        os.environ.get("FREEROUTING_THREADS", "1"),
        "-l",
        "en",
        "--router.layers.routable=true,false,false,true",
    ]
    if sys.platform.startswith("linux") and not os.environ.get("DISPLAY"):
        xvfb_run = shutil.which("xvfb-run")
        if xvfb_run is None:
            raise SystemExit("headless Linux requires xvfb-run")
        command = [xvfb_run, "-a", *command]
    return command


def main() -> None:
    FAB.mkdir(exist_ok=True)
    board, _keepalive = build_placed_board()
    if os.environ.get("INKBOT_PLACE_ONLY") == "1":
        print(f"placed {len(list(board.GetFootprints()))} footprints")
        return

    if not pcbnew.ExportSpecctraDSN(board, str(DSN)):
        raise SystemExit(f"failed to export Specctra DSN: {DSN}")
    mark_power_layers(DSN)

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

    import_freerouting_session(board, SES)
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
    if unconnected:
        raise SystemExit(f"routing left {unconnected} open ratsnest connections")
    layout_route.export_fab()


if __name__ == "__main__":
    main()

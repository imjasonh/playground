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

import json
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
    tokens = re.finditer(r'\(|\)|"(?:\\.|[^"\\])*"|[^\s()]+', text)
    for match in tokens:
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
    """Import Freerouting wires and vias into a board through pcbnew.

    KiCad 7 exposes ``ImportSpecctraSES(filename)`` only for an active GUI
    board. A standalone Python process has no active board, so this importer
    applies the SES ``network_out`` routes to the board object directly.
    """
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
    units_per_micrometer = int(str(resolution[2]))
    nanometers_per_unit = 1000 / units_per_micrometer
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
                width = max(coordinate(path_form[2]), layout_route.mm(0.15))
                values = path_form[3:]
                if len(values) % 2:
                    raise ValueError(f"odd coordinate count for net {net_name}")
                points = [
                    pcbnew.VECTOR2I(coordinate(values[i]), coordinate(values[i + 1], True))
                    for i in range(0, len(values), 2)
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
                via.SetWidth(diameter_um * 1000)
                via.SetDrill(drill_um * 1000)
                via.SetLayerPair(copper_layers[start_layer], copper_layers[end_layer])
                via.SetNet(net)
                board.Add(via)
                via_count += 1
    print(f"imported {wire_count} track segments and {via_count} vias from {path}")


def build_placed_board() -> tuple[pcbnew.BOARD, list[pcbnew.SHAPE_POLY_SET]]:
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

    settings = board.GetDesignSettings()
    settings.SetCustomTrackWidth(layout_route.TRACK_W)
    settings.SetCustomViaSize(layout_route.VIA_D)
    settings.SetCustomViaDrill(layout_route.VIA_DRILL)
    settings.m_ViasDimensionsList.clear()
    settings.m_ViasDimensionsList.append(
        pcbnew.VIA_DIMENSION(layout_route.VIA_D, layout_route.VIA_DRILL)
    )
    settings.SetViaSizeIndex(0)

    def pad_center(reference: str, pad_number: str) -> pcbnew.VECTOR2I:
        for pad in placed[reference].Pads():
            if pad.GetNumber() == pad_number:
                return pad.GetCenter()
        raise ValueError(f"missing pad {reference}.{pad_number}")

    def add_locked_via(position: pcbnew.VECTOR2I, net_name: str) -> None:
        via = pcbnew.PCB_VIA(board)
        via.SetPosition(position)
        via.SetWidth(layout_route.VIA_D)
        via.SetDrill(layout_route.VIA_DRILL)
        via.SetLayerPair(pcbnew.F_Cu, pcbnew.B_Cu)
        via.SetNet(netmap[net_name])
        via.SetLocked(True)
        board.Add(via)

    def add_locked_track(
        start: pcbnew.VECTOR2I,
        end: pcbnew.VECTOR2I,
        net_name: str,
        layer: int = pcbnew.B_Cu,
        width: int = layout_route.TRACK_W,
    ) -> None:
        track = pcbnew.PCB_TRACK(board)
        track.SetStart(start)
        track.SetEnd(end)
        track.SetWidth(width)
        track.SetLayer(layer)
        track.SetNet(netmap[net_name])
        track.SetLocked(True)
        board.Add(track)

    for reference, pad_number in (("TP4", "1"), ("U3", "6")):
        add_locked_via(pad_center(reference, pad_number), layout_route.VSYS)

    u5_vsys = pad_center("U5", "4")
    u5_via = pcbnew.VECTOR2I(u5_vsys.x - layout_route.mm(0.85), u5_vsys.y)
    add_locked_track(u5_vsys, u5_via, layout_route.VSYS)
    add_locked_via(u5_via, layout_route.VSYS)

    u5_ntc = pad_center("U5", "13")
    ntc_corner = pcbnew.VECTOR2I(layout_route.mm(11.4), u5_ntc.y)
    ntc_via = pcbnew.VECTOR2I(layout_route.mm(11.7), layout_route.mm(63.7))
    for start, end in ((u5_ntc, ntc_corner), (ntc_corner, ntc_via)):
        add_locked_track(start, end, "/NTC_SENSE", width=layout_route.mm(0.15))
    add_locked_via(ntc_via, "/NTC_SENSE")

    u1_ntc = pad_center("U1", "20")
    u1_ntc_via = pcbnew.VECTOR2I(layout_route.mm(28.2), u1_ntc.y)
    add_locked_track(u1_ntc, u1_ntc_via, "/NTC_SENSE", width=layout_route.mm(0.15))
    add_locked_via(u1_ntc_via, "/NTC_SENSE")
    ntc_path = [
        ntc_via,
        pcbnew.VECTOR2I(layout_route.mm(12.5), layout_route.mm(81.5)),
        pcbnew.VECTOR2I(layout_route.mm(28.2), layout_route.mm(81.5)),
        u1_ntc_via,
    ]
    for start, end in zip(ntc_path, ntc_path[1:]):
        add_locked_track(start, end, "/NTC_SENSE", layer=pcbnew.F_Cu)

    clamp_path = [
        pad_center("U5", "16"),
        pcbnew.VECTOR2I(layout_route.mm(11.3), layout_route.mm(66.25)),
        pcbnew.VECTOR2I(layout_route.mm(11.3), layout_route.mm(69.0)),
        pad_center("C7", "1"),
    ]
    for start, end in zip(clamp_path, clamp_path[1:]):
        add_locked_track(
            start,
            end,
            "/QI_CLAMP2",
            width=layout_route.mm(0.15),
        )

    for x, y in ((9.8005, 69.1673), (7.6957, 63.3848)):
        add_locked_via(
            pcbnew.VECTOR2I(layout_route.mm(x), layout_route.mm(y)),
            layout_route.GND,
        )

    keepalive: list[pcbnew.SHAPE_POLY_SET] = []

    def add_plane(layer: int, net_name: str) -> None:
        zone = pcbnew.ZONE(board)
        zone.SetLayer(layer)
        zone.SetNet(netmap[net_name])
        zone.SetLocalClearance(layout_route.mm(layout_route.CLEAR))
        zone.SetMinThickness(layout_route.mm(0.2))
        zone.SetPadConnection(pcbnew.ZONE_CONNECTION_FULL)
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
        keepalive.append(outline)
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
    keepalive.append(outline)
    board.Add(antenna_keepout)

    cutout_keepout = pcbnew.ZONE(board)
    cutout_keepout.SetIsRuleArea(True)
    cutout_keepout.SetDoNotAllowCopperPour(True)
    cutout_keepout.SetDoNotAllowTracks(True)
    cutout_keepout.SetDoNotAllowVias(True)
    cutout_keepout.SetLayerSet(layers)
    outline = pcbnew.SHAPE_POLY_SET()
    outline.NewOutline()
    for x, y in ((13.5, 59.5), (46.5, 59.5), (46.5, 80.5), (13.5, 80.5)):
        outline.Append(layout_route.mm(x), layout_route.mm(y))
    cutout_keepout.SetOutline(outline)
    keepalive.append(outline)
    board.Add(cutout_keepout)

    board.BuildConnectivity()
    fill_zones(board)
    pcbnew.SaveBoard(str(BOARD), board)
    return board, keepalive


def mark_inner_layers_as_power(path: Path) -> None:
    """Mark the two internal planes as non-routable in a KiCad DSN export."""
    text = path.read_text()
    for layer_name in ("In1.Cu", "In2.Cu"):
        signal = f"    (layer {layer_name}\n      (type signal)"
        power = f"    (layer {layer_name}\n      (type power)"
        if text.count(signal) != 1:
            raise ValueError(f"cannot find the {layer_name} layer in {path}")
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
        os.environ.get("FREEROUTING_PASSES", "100"),
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
    if not pcbnew.ExportSpecctraDSN(board, str(DSN)):
        raise SystemExit(f"failed to export Specctra DSN: {DSN}")
    mark_inner_layers_as_power(DSN)

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
    print(f"imported {SES}; open ratsnest connections: {unconnected}")
    layout_route.export_fab()


if __name__ == "__main__":
    main()

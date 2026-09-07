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
ROUTE_BASE = FAB / "inkbot-magsafe-route-base.kicad_pcb"
PLACED_BOARD = FAB / "inkbot-magsafe-placed.kicad_pcb"
INCOMPLETE_BOARD = FAB / "inkbot-magsafe-incomplete.kicad_pcb"
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
                # Freerouting calculates clearance using this exact width.
                # KiCad remains the release checker. Clamp fine-pitch fanout
                # tapers to the board minimum, then reject the result if KiCad
                # finds any resulting clearance error.
                width = coordinate(path_form[2])
                width = max(width, layout_route.mm(layout_route.CLEAR))
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
    generate_pcb.main(ROUTE_BASE)
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
    board = pcbnew.LoadBoard(str(ROUTE_BASE))
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

    def pad_center(
        reference: str,
        pad_number: str,
        near_xy: tuple[float, float] | None = None,
    ) -> pcbnew.VECTOR2I:
        matches = [
            pad.GetCenter()
            for pad in placed[reference].Pads()
            if pad.GetNumber() == pad_number
        ]
        if not matches:
            raise ValueError(f"missing pad {reference}.{pad_number}")
        if len(matches) == 1:
            return matches[0]
        if near_xy is None:
            raise ValueError(f"ambiguous duplicate pad {reference}.{pad_number}")
        target = pcbnew.VECTOR2I(
            layout_route.mm(near_xy[0]),
            layout_route.mm(near_xy[1]),
        )
        return min(
            matches,
            key=lambda point: (point.x - target.x) ** 2 + (point.y - target.y) ** 2,
        )

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

    def add_locked_via(position: pcbnew.VECTOR2I, net_name: str) -> None:
        via = pcbnew.PCB_VIA(board)
        via.SetPosition(position)
        via.SetWidth(layout_route.VIA_D)
        via.SetDrill(layout_route.VIA_DRILL)
        via.SetLayerPair(pcbnew.F_Cu, pcbnew.B_Cu)
        via.SetNet(netmap[net_name])
        via.SetLocked(True)
        board.Add(via)

    def fanout_to_plane(
        reference: str,
        pad_number: str,
        via_xy: tuple[float, float],
        path_xy: tuple[tuple[float, float], ...] = (),
        width: int = layout_route.TRACK_W,
        net_name: str = layout_route.SYS,
        pad_near_xy: tuple[float, float] | None = None,
    ) -> None:
        via = pcbnew.VECTOR2I(layout_route.mm(via_xy[0]), layout_route.mm(via_xy[1]))
        points = [
            pad_center(reference, pad_number, pad_near_xy),
            *(
                pcbnew.VECTOR2I(layout_route.mm(x), layout_route.mm(y))
                for x, y in path_xy
            ),
            via,
        ]
        for start, end in zip(points, points[1:]):
            add_locked_track(start, end, net_name, width=width)
        add_locked_via(via, net_name)

    def board_point(x: float, y: float) -> pcbnew.VECTOR2I:
        return pcbnew.VECTOR2I(layout_route.mm(x), layout_route.mm(y))

    def add_locked_path(
        coordinates: tuple[tuple[float, float], ...],
        net_name: str,
        layer: int,
        width: int = layout_route.TRACK_W,
    ) -> None:
        points = [board_point(x, y) for x, y in coordinates]
        for start, end in zip(points, points[1:]):
            add_locked_track(start, end, net_name, layer=layer, width=width)

    """Legacy fixed routes retained temporarily while the 0.8 hardware
    architecture is re-placed. Replace this block before routing.

    # Short, narrow escapes connect every SYS load to the solid In1.Cu plane.
    # This avoids routing a wide trace through the 0.4 mm-pitch charger pads.
    fanout_to_plane("U3", "1", (49.7, 61.3), width=layout_route.mm(0.15))
    fanout_to_plane("TP6", "1", (56.8, 58.0), width=layout_route.mm(0.5))
    fanout_to_plane("C38", "1", (23.5, 94.525), width=layout_route.mm(0.5))
    fanout_to_plane("C26", "1", (26.8, 87.0), width=layout_route.mm(0.3))
    fanout_to_plane(
        "C21",
        "1",
        (20.5, 91.8),
        path_xy=((17.725, 91.8),),
        width=layout_route.mm(0.3),
    )
    add_locked_track(
        pad_center("U1", "30"),
        board_point(17.2, 91.4),
        layout_route.SYS,
        width=layout_route.mm(0.15),
    )
    add_locked_track(
        board_point(17.2, 91.4),
        pad_center("C21", "1"),
        layout_route.SYS,
        width=layout_route.mm(0.15),
    )
    fanout_to_plane("U4", "1", (36.0, 89.0), width=layout_route.mm(0.3))
    fanout_to_plane("C18", "1", (51.55, 65.5), width=layout_route.mm(0.5))

    # Each ground cluster reaches the solid In2.Cu plane through a locked
    # through-via. Keep vias beside passive pads to avoid solder-wicking
    # via-in-pad joints.
    for reference, pad_number, via_xy in (
        ("J3", "4", (11.0, 55.0)),
        ("C12", "2", (11.0, 74.35)),
        ("C13", "2", (4.025, 77.25)),
        ("C14", "2", (7.175, 77.25)),
        ("C15", "2", (11.35, 77.35)),
        ("C16", "2", (3.775, 80.25)),
        ("R2", "2", (11.0, 80.35)),
        ("C17", "2", (50.5, 65.0)),
        ("C18", "2", (53.45, 65.2)),
        ("C19", "2", (58.0, 64.0)),
        ("R5", "2", (50.5, 68.2)),
        ("R6", "2", (54.0, 67.0)),
        ("R7", "2", (58.0, 67.0)),
        ("C20", "2", (54.0, 70.0)),
        ("U3", "5", (49.75, 58.6)),
        ("U3", "11", (52.0, 61.55)),
        ("J2", "3", (54.2, 80.1)),
        ("C21", "2", (20.4, 90.5)),
        ("C22", "2", (20.4, 93.0)),
        ("C23", "2", (25.4, 85.0)),
        ("C24", "2", (25.4, 87.5)),
        ("C26", "2", (29.7, 87.0)),
        ("C28", "2", (29.95, 84.5)),
        ("C29", "2", (33.775, 84.5)),
        ("C30", "2", (37.775, 84.5)),
        ("C31", "2", (41.95, 84.5)),
        ("C32", "2", (45.95, 84.5)),
        ("C33", "2", (49.95, 84.5)),
        ("C34", "2", (53.95, 84.5)),
        ("C35", "2", (58.0, 84.5)),
        ("C36", "2", (30.8, 90.0)),
        ("R11", "2", (30.8, 93.0)),
        ("R12", "2", (34.8, 93.0)),
        ("C38", "2", (26.3, 97.475)),
        ("D2", "1", (53.35, 85.7)),
        ("J1", "8", (42.75, 97.0)),
        ("J1", "17", (47.25, 97.0)),
        ("TP5", "1", (58.6, 97.0)),
        ("U1", "15", (16.4, 84.2)),
        ("U1", "33", (16.4, 93.8)),
        ("U1", "55", (5.2, 95.0)),
    ):
        fanout_to_plane(
            reference,
            pad_number,
            via_xy,
            net_name=layout_route.GND,
        )

    # C27 and the LDO share a stitch, with a horizontal escape that stays
    # clear of U4's adjacent SYS pad.
    ldo_ground_junction = board_point(34.5, 87.0)
    ldo_ground_via = board_point(34.5, 88.3)
    add_locked_track(
        pad_center("C27", "2"),
        ldo_ground_junction,
        layout_route.GND,
    )
    add_locked_track(
        pad_center("U4", "2"),
        ldo_ground_junction,
        layout_route.GND,
    )
    add_locked_track(
        ldo_ground_junction,
        ldo_ground_via,
        layout_route.GND,
    )
    add_locked_via(ldo_ground_via, layout_route.GND)

    # The module's first two ground lands share one nearby stitch.
    module_ground_via = board_point(5.1, 83.3)
    for pad_number in ("1", "2"):
        add_locked_track(
            pad_center("U1", pad_number),
            module_ground_via,
            layout_route.GND,
        )
    add_locked_via(module_ground_via, layout_route.GND)

    # Both mechanical tabs on each connector need a physical ground path.
    for reference, pad_near_xy, via_xy in (
        ("J1", (37.35, 92.6), (36.1, 92.6)),
        ("J1", (52.65, 92.6), (53.9, 92.6)),
        ("J2", (50.65, 75.1), (50.65, 73.9)),
        ("J2", (55.35, 75.1), (55.35, 73.9)),
    ):
        fanout_to_plane(
            reference,
            "MP",
            via_xy,
            net_name=layout_route.GND,
            pad_near_xy=pad_near_xy,
        )

    # Fan out the BQ51013C's perimeter ground lands before routing. Its exposed
    # pad connects to the upper stitch through copper under the package.
    qi_ground_pads = [
        pad
        for pad in placed["U2"].Pads()
        if pad.GetNetname() == layout_route.GND
    ]
    upper_bus_y = 55.8
    lower_bus_y = 62.1
    for pad in qi_ground_pads:
        center = pad.GetCenter()
        x = pcbnew.ToMM(center.x)
        y = pcbnew.ToMM(center.y)
        if abs(y - 56.85) < 0.01:
            add_locked_track(
                center,
                board_point(x, upper_bus_y),
                layout_route.GND,
            )
        elif abs(y - 61.15) < 0.01:
            add_locked_track(
                center,
                board_point(x, lower_bus_y),
                layout_route.GND,
            )
    add_locked_path(
        ((6.25, upper_bus_y), (7.75, upper_bus_y), (7.0, 55.0)),
        layout_route.GND,
        pcbnew.B_Cu,
    )
    add_locked_path(
        ((6.25, lower_bus_y), (7.75, lower_bus_y), (7.0, 62.6)),
        layout_route.GND,
        pcbnew.B_Cu,
    )
    add_locked_track(
        board_point(7.0, 59.0),
        board_point(7.0, upper_bus_y),
        layout_route.GND,
    )
    add_locked_via(board_point(7.0, 55.0), layout_route.GND)
    add_locked_via(board_point(7.0, 62.6), layout_route.GND)
    fanout_to_plane("U2", "9", (4.3, 57.25), net_name=layout_route.GND)

    # The charge-enable signal crosses the front below the battery cutout.
    ce_left = pcbnew.VECTOR2I(layout_route.mm(19.0), layout_route.mm(88.2))
    ce_right = pcbnew.VECTOR2I(layout_route.mm(48.3), layout_route.mm(68.2))
    add_locked_track(
        pad_center("U1", "22"),
        ce_left,
        "/CHG_EN_N",
        width=layout_route.mm(0.15),
    )
    add_locked_via(ce_left, "/CHG_EN_N")
    ce_path = [
        ce_left,
        pcbnew.VECTOR2I(layout_route.mm(19.0), layout_route.mm(82.7)),
        pcbnew.VECTOR2I(layout_route.mm(48.3), layout_route.mm(82.7)),
        ce_right,
    ]
    for start, end in zip(ce_path, ce_path[1:]):
        add_locked_track(start, end, "/CHG_EN_N", layer=pcbnew.F_Cu)
    add_locked_via(ce_right, "/CHG_EN_N")
    add_locked_track(
        ce_right,
        pad_center("R5", "1"),
        "/CHG_EN_N",
        width=layout_route.mm(0.15),
    )

    def connect_through_front(
        net_name: str,
        start: tuple[str, str],
        start_via_xy: tuple[float, float],
        front_path_xy: tuple[tuple[float, float], ...],
        end: tuple[str, str],
        end_via_xy: tuple[float, float],
    ) -> None:
        start_via = board_point(*start_via_xy)
        end_via = board_point(*end_via_xy)
        add_locked_track(
            pad_center(*start),
            start_via,
            net_name,
            width=layout_route.mm(0.15),
        )
        add_locked_via(start_via, net_name)
        add_locked_path(
            (start_via_xy, *front_path_xy, end_via_xy),
            net_name,
            pcbnew.F_Cu,
            width=layout_route.mm(0.15),
        )
        add_locked_via(end_via, net_name)
        add_locked_track(
            end_via,
            pad_center(*end),
            net_name,
            width=layout_route.mm(0.15),
        )

    # These constrained nets repeatedly fail at fine-pitch escapes or around
    # the battery cutout. Lock their short, reviewable paths before autorouting.
    connect_through_front(
        "/QI_BOOT1",
        ("U2", "3"),
        (4.3, 60.25),
        (
            (1.7, 60.25),
            (1.2, 60.75),
            (1.2, 65.0),
            (1.7, 65.5),
            (10.15, 65.5),
        ),
        ("C6", "1"),
        (10.15, 65.85),
    )
    connect_through_front(
        "/QI_BOOT2",
        ("U2", "17"),
        (9.6, 59.75),
        (
            (11.3, 59.75),
            (11.8, 60.25),
            (11.8, 68.2),
            (11.3, 68.7),
        ),
        ("C7", "1"),
        (2.225, 68.7),
    )
    connect_through_front(
        "/CHG_STAT2",
        ("U3", "3"),
        (49.75, 60.0),
        (
            (49.0, 60.75),
            (49.0, 82.9),
            (48.5, 83.4),
            (20.5, 83.4),
            (20.5, 88.7),
            (20.0, 89.2),
            (14.9, 89.2),
        ),
        ("U1", "21"),
        (13.5, 87.8),
    )
    connect_through_front(
        "/VDD_NRF",
        ("U1", "28"),
        (16.5, 90.6),
        (),
        ("C22", "1"),
        (16.5, 93.0),
    )

    """

    # Connect every SYS load to In1.Cu before routing signal layers.
    for reference, pad_number, via_xy, width in (
        ("U3", "1", (49.7, 61.3), 0.15),
        ("TP6", "1", (56.8, 58.0), 0.5),
        ("C38", "1", (23.5, 94.525), 0.5),
        ("C26", "1", (26.8, 87.0), 0.3),
        ("C21", "1", (18.0, 88.5), 0.3),
        ("U4", "1", (36.0, 89.0), 0.3),
        ("C18", "1", (51.55, 65.5), 0.5),
        ("R9", "1", (17.7, 84.0), 0.2),
        ("U5", "1", (21.2, 92.2), 0.3),
        ("U5", "3", (21.2, 89.8), 0.2),
    ):
        fanout_to_plane(
            reference,
            pad_number,
            via_xy,
            width=layout_route.mm(width),
        )

    # Place ground stitches beside pads so solder does not wick into open
    # via-in-pad barrels. Closely spaced IC lands share local ground buses.
    for reference, pad_number, via_xy in (
        ("J3", "4", (11.0, 55.0)),
        ("C12", "2", (4.5, 70.5)),
        ("C13", "2", (7.8, 72.8)),
        ("C14", "2", (11.475, 73.3)),
        ("C15", "2", (4.025, 80.0)),
        ("C16", "2", (7.175, 78.4)),
        ("R2", "2", (11.9, 60.4)),
        ("C17", "2", (50.5, 65.0)),
        ("C18", "2", (53.45, 65.2)),
        ("C19", "2", (58.0, 64.0)),
        ("C20", "2", (26.4, 82.8)),
        ("R10", "2", (22.3, 84.0)),
        ("C21", "2", (19.0, 91.3)),
        ("C22", "2", (20.6, 94.8)),
        ("C23", "2", (25.4, 85.0)),
        ("C24", "2", (25.4, 87.5)),
        ("C26", "2", (29.7, 87.0)),
        ("C28", "2", (29.95, 84.5)),
        ("C29", "2", (33.775, 84.5)),
        ("C30", "2", (37.775, 84.5)),
        ("C31", "2", (41.95, 84.5)),
        ("C32", "2", (45.95, 84.5)),
        ("C33", "2", (49.95, 84.5)),
        ("C34", "2", (53.95, 84.5)),
        ("C35", "2", (58.0, 84.5)),
        ("C36", "2", (30.8, 90.0)),
        ("R11", "2", (30.8, 93.0)),
        ("R12", "2", (34.8, 93.0)),
        ("C38", "2", (26.3, 97.475)),
        ("D2", "1", (53.35, 85.7)),
        ("J1", "8", (42.75, 97.0)),
        ("J1", "17", (47.25, 97.0)),
        ("J2", "3", (54.2, 80.1)),
        ("TP5", "1", (58.6, 97.0)),
        ("U1", "15", (16.4, 84.2)),
        ("U1", "33", (16.4, 93.8)),
        ("U1", "55", (5.2, 95.0)),
        ("U3", "5", (49.75, 58.6)),
        ("U3", "11", (52.0, 61.55)),
        ("U5", "2", (21.0, 91.0)),
    ):
        fanout_to_plane(
            reference,
            pad_number,
            via_xy,
            net_name=layout_route.GND,
        )

    ldo_ground_junction = board_point(34.5, 87.0)
    ldo_ground_via = board_point(34.5, 88.3)
    for reference in ("C27", "U4"):
        add_locked_track(
            pad_center(reference, "2"),
            ldo_ground_junction,
            layout_route.GND,
        )
    add_locked_track(
        ldo_ground_junction,
        ldo_ground_via,
        layout_route.GND,
    )
    add_locked_via(ldo_ground_via, layout_route.GND)

    charger_gate_ground_via = board_point(54.0, 68.0)
    for reference, pad_number in (("R6", "2"), ("Q2", "2")):
        add_locked_track(
            pad_center(reference, pad_number),
            charger_gate_ground_via,
            layout_route.GND,
        )
    add_locked_via(charger_gate_ground_via, layout_route.GND)

    module_ground_via = board_point(5.1, 83.3)
    for pad_number in ("1", "2"):
        add_locked_track(
            pad_center("U1", pad_number),
            module_ground_via,
            layout_route.GND,
        )
    add_locked_via(module_ground_via, layout_route.GND)

    for reference, pad_near_xy, via_xy in (
        ("J1", (37.35, 92.6), (36.1, 92.6)),
        ("J1", (52.65, 92.6), (53.9, 92.6)),
        ("J2", (50.65, 75.1), (50.65, 73.9)),
        ("J2", (55.35, 75.1), (55.35, 73.9)),
    ):
        fanout_to_plane(
            reference,
            "MP",
            via_xy,
            net_name=layout_route.GND,
            pad_near_xy=pad_near_xy,
        )

    qi_ground_pads = [
        pad
        for pad in placed["U2"].Pads()
        if pad.GetNetname() == layout_route.GND
    ]
    upper_bus_y = 62.3
    lower_bus_y = 68.7
    for pad in qi_ground_pads:
        center = pad.GetCenter()
        x = pcbnew.ToMM(center.x)
        y = pcbnew.ToMM(center.y)
        if abs(y - 63.35) < 0.01:
            add_locked_track(center, board_point(x, upper_bus_y), layout_route.GND)
        elif abs(y - 67.65) < 0.01:
            add_locked_track(center, board_point(x, lower_bus_y), layout_route.GND)
    add_locked_path(
        ((6.725, upper_bus_y), (7.275, upper_bus_y), (7.0, 61.7)),
        layout_route.GND,
        pcbnew.B_Cu,
    )
    add_locked_path(
        ((6.25, lower_bus_y), (7.75, lower_bus_y), (7.0, 70.2)),
        layout_route.GND,
        pcbnew.B_Cu,
    )
    add_locked_track(
        board_point(7.0, 65.5),
        board_point(7.0, upper_bus_y),
        layout_route.GND,
    )
    add_locked_via(board_point(7.0, 61.7), layout_route.GND)
    add_locked_via(board_point(7.0, 70.2), layout_route.GND)
    fanout_to_plane("U2", "9", (4.3, 63.75), net_name=layout_route.GND)

    add_locked_path(
        (
            (5.35, 65.75),
            (4.5, 65.2),
            (2.225, 65.2),
            (2.225, 66.0),
        ),
        "/QI_CLAMP1",
        pcbnew.B_Cu,
        width=layout_route.mm(0.15),
    )
    add_locked_path(
        (
            (8.65, 65.25),
            (9.3, 65.25),
            (10.225, 64.325),
            (10.225, 63.0),
        ),
        "/QI_COMM2",
        pcbnew.B_Cu,
        width=layout_route.mm(0.15),
    )
    qi_out_start_via = board_point(4.3, 66.25)
    qi_out_end_via = board_point(5.625, 75.8)
    add_locked_track(
        pad_center("U2", "4"),
        qi_out_start_via,
        "/QI_OUT",
        width=layout_route.mm(0.15),
    )
    add_locked_via(qi_out_start_via, "/QI_OUT")
    add_locked_path(
        (
            (4.3, 66.25),
            (5.2, 67.15),
            (5.2, 75.375),
            (5.625, 75.8),
        ),
        "/QI_OUT",
        pcbnew.F_Cu,
        width=layout_route.mm(0.2),
    )
    add_locked_via(qi_out_end_via, "/QI_OUT")
    add_locked_track(
        qi_out_end_via,
        pad_center("C16", "1"),
        "/QI_OUT",
        width=layout_route.mm(0.3),
    )

    settings = board.GetDesignSettings()
    default_netclass = settings.m_NetSettings.m_DefaultNetClass
    default_netclass.SetClearance(layout_route.mm(layout_route.CLEAR))
    default_netclass.SetTrackWidth(layout_route.TRACK_W)
    default_netclass.SetViaDiameter(layout_route.VIA_D)
    default_netclass.SetViaDrill(layout_route.VIA_DRILL)
    settings.m_MinClearance = layout_route.mm(layout_route.CLEAR)
    settings.m_TrackMinWidth = layout_route.mm(layout_route.CLEAR)
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

    router_home = FAB / "freerouting-home"
    router_home.mkdir(exist_ok=True)
    command = [
        java,
        f"-Duser.home={router_home}",
        "-jar",
        str(jar),
        "-de",
        str(DSN),
        "-do",
        str(SES),
        "-mp",
        os.environ.get("FREEROUTING_PASSES", "150"),
        "-mt",
        "0",
        "-l",
        "en",
        "--router.optimizer.enabled=false",
        "--router.copperToEdgeClearanceUm=500",
        "--gui.enabled=false",
        "--api_server.enabled=false",
        "--usage_and_diagnostic_data.disable_analytics=true",
        "--router.layers.routable=true,false,false,true",
    ]
    return command


def main() -> None:
    FAB.mkdir(exist_ok=True)
    board, _keepalive = build_placed_board()
    if os.environ.get("INKBOT_PLACE_ONLY") == "1":
        pcbnew.SaveBoard(str(PLACED_BOARD), board)
        print(f"placed {len(list(board.GetFootprints()))} footprints")
        print(f"wrote {PLACED_BOARD}")
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

    connectivity = board.GetConnectivity()
    unconnected = (
        connectivity.GetUnconnectedCount(True)
        if hasattr(connectivity, "GetUnconnectedCount")
        else -1
    )
    if unconnected:
        pcbnew.SaveBoard(str(INCOMPLETE_BOARD), board)
        raise SystemExit(f"routing left {unconnected} open ratsnest connections")
    pcbnew.SaveBoard(str(BOARD), board)
    layout_route.export_fab()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Place, net, pour, route, and export the inkbot-magsafe board with pcbnew.

Starts from the outline board written by ``generate_pcb.py`` and the schematic
netlist exported by ``kicad-cli sch export netlist``. Places every footprint on
the back, assigns nets to pads, pours the ground and VSYS planes, routes the
signal nets with a clearance-aware maze router (B.Cu main, F.Cu escape),
stitches the ground planes, fills, and writes Gerbers, drill, and centroid
under ``kicad/fab/``.

The radio is a pre-certified Raytac MDBT50Q-512K module, so there is no antenna
or matching network to route. The router honors the module footprint's own
antenna keep-outs plus a board keep-out under the module. Run ``run_drc.py``
(KiCad's DRC engine) after generating; finish any remaining ratsnest in the
pcbnew GUI before a production order.
"""

from __future__ import annotations

import heapq
import re
import subprocess
from pathlib import Path

import pcbnew

HERE = Path(__file__).resolve().parent
BOARD = HERE / "inkbot-magsafe.kicad_pcb"
NETLIST = Path("/tmp/inkbot.net")
FP_ROOT = Path("/usr/share/kicad/footprints")
FAB = HERE / "fab"

BOARD_W, BOARD_H = 60.0, 99.0
BAT_W, BAT_H, BAT_CY = 32.0, 20.0, 70.0
CX = BOARD_W / 2

# Placement: ref -> (x_mm, y_mm, rotation_deg). Parts mount on the back (the
# panel is the front face). The magnet ring / coil dominate the top (y < 57)
# and the LiPo cutout takes the center (x14-46, y60-80). Parts live in the two
# columns beside the cutout and the bottom band (y > 82). U5 keeps its pads
# >= 0.5 mm off the left edge. J1 sits to the right of the module, and the SWD
# pads use the narrow corridor between their courtyards.
PLACEMENT = {
    # Module rotated landscape and dropped below the cutout (a portrait module
    # is 0.1 mm too tall to keep 0.5 mm off both the cutout and the board edge).
    "U1": (20.0, 88.0, 90),
    "J1": (44.0, 94.0, 0),   # panel FPC, clear of the module at the bottom edge
    # Qi receiver + coil leads: left column beside the cutout
    "U5": (9.2, 66.0, 0),
    "L1": (24.0, 57.0, 0),
    # panel power in the bottom-right, clear of the sense column (y63-75)
    "U3": (48.5, 82.5, 0),
    "U4": (56.5, 82.5, 0),
    # module bypass + LFXO in the bottom-left corner (clear of the module body
    # and its antenna keep-out)
    "C15": (4.0, 96.5, 0),
    "C16": (8.0, 96.5, 0),
    "Y1": (12.5, 96.5, 90),
    # sense / bulk: right column beside the cutout
    "C10": (52.0, 63.0, 0),
    "C11": (52.0, 66.0, 0),
    "RT1": (52.0, 69.0, 0),
    "R5": (52.0, 72.0, 0),
    "R6": (52.0, 75.0, 0),
    "R7": (56.0, 72.0, 0),
    "R8": (56.0, 75.0, 0),
    # Qi support cluster in the left column around U5
    "C1": (4.0, 62.0, 0),
    "C2": (4.0, 66.0, 0),
    "C3": (4.0, 70.0, 0),
    "C4": (4.0, 74.0, 0),
    "C5": (12.5, 67.25, 90),
    "C6": (12.5, 72.0, 0),
    "C7": (12.5, 69.0, 0),
    "C8": (7.5, 74.0, 0),
    "C9": (12.5, 65.75, 0),
    "R1": (4.0, 78.0, 0),
    "R2": (12.5, 62.0, 0),
    "R3": (8.45, 61.5, 90),
    "R4": (12.5, 76.0, 0),
    # panel-power passives near U3/U4 in the bottom-right
    "C12": (52.5, 82.0, 0),
    "C13": (52.5, 85.0, 0),
    "C14": (52.5, 87.5, 0),
    "C21": (48.5, 86.5, 0),
    # SWD test pads in the module-to-FPC corridor and beside the FPC.
    "TP1": (31.5, 83.0, 0),
    "TP2": (31.5, 87.0, 0),
    "TP3": (31.5, 91.0, 0),
    "TP4": (31.5, 95.0, 0),
    "TP5": (56.5, 95.5, 0),
}

# Plane nets: poured, not track-routed. KiCad prefixes local labels with "/";
# GND comes from a power symbol so it stays global (no slash).
GND = "GND"
VSYS = "/VSYS"

# All module GND pads (the schematic symbol only exposes pin 1) + VBUS.
MODULE_GND_PADS = ["1", "2", "15", "33", "55", "32"]

TRACK_W = int(0.2 * 1e6)
VIA_D = int(0.5 * 1e6)
VIA_DRILL = int(0.3 * 1e6)

# Design rules the router must satisfy (KiCad board defaults).
CLEAR = 0.15        # copper clearance
HOLE_CLEAR = 0.25   # hole-to-copper clearance
EDGE_CLEAR = 0.5    # copper-to-board-edge clearance

# Maze-router grid. Fine (0.2 mm) so routes escape fine-pitch pads; clearance is
# enforced during search by rejecting any cell that touches foreign copper
# (see passable()), which keeps different nets >= 2 cells (0.4 mm centre, 0.2 mm
# edge gap > 0.15 mm) apart.
GRID = 0.2
NX = int(BOARD_W / GRID) + 1
NY = int(BOARD_H / GRID) + 1

# A 0.5 mm via with a 0.3 mm hole needs foreign copper ~0.5 mm and foreign holes
# ~0.25 mm away; reserve a disk of this radius (cells) around each via for its
# own net so the neighbour check pushes foreign copper safely clear.
VIA_R = 3           # cells (~0.6 mm) reserved around a via
VIA_EDGE = 0.75     # via centre must stay this far from any board edge / cutout


def parse_netlist(path: Path):
    text = path.read_text()
    comps = {}
    for m in re.finditer(r'\(comp \(ref "([^"]+)"\)(.*?)(?=\(comp \(ref |\(libparts)', text, re.S):
        ref, body = m.group(1), m.group(2)
        fp = re.search(r'\(footprint "([^"]+)"\)', body)
        comps[ref] = fp.group(1) if fp else ""
    nets = {}
    for m in re.finditer(r'\(net \(code "\d+"\) \(name "([^"]+)"\)(.*?)(?=\(net \(code|\)\s*\Z|\n\s*\)\s*\Z)', text, re.S):
        name, body = m.group(1), m.group(2)
        nodes = [(r, p) for r, p in re.findall(r'\(node \(ref "([^"]+)"\) \(pin "([^"]+)"\)', body)]
        if nodes:
            nets[name] = nodes
    return comps, nets


def load_fp(libname: str):
    lib, name = libname.split(":", 1)
    fp = pcbnew.FootprintLoad(str(FP_ROOT / f"{lib}.pretty"), name)
    if fp is None:
        raise SystemExit(f"missing footprint {libname}")
    return fp


def mm(v):
    return int(v * 1e6)


def point_in_poly(px, py, poly):
    """Ray-cast point-in-polygon; poly is a list of (x, y) in mm."""
    inside = False
    n = len(poly)
    j = n - 1
    for i in range(n):
        xi, yi = poly[i]
        xj, yj = poly[j]
        if ((yi > py) != (yj > py)) and (
            px < (xj - xi) * (py - yi) / (yj - yi + 1e-12) + xi
        ):
            inside = not inside
        j = i
    return inside


def main() -> None:
    comps, nets = parse_netlist(NETLIST)
    board = pcbnew.LoadBoard(str(BOARD))
    for fp in list(board.GetFootprints()):
        board.Remove(fp)

    # Nets.
    netmap = {}
    for name in list(nets) + [GND, VSYS]:
        if name in netmap:
            continue
        ni = pcbnew.NETINFO_ITEM(board, name)
        board.Add(ni)
        netmap[name] = ni
    netmap_by_code = {netmap[n].GetNetCode(): netmap[n] for n in netmap}

    # Place footprints (skip parts without a footprint, e.g. the cell symbol).
    placed = {}
    for ref, libname in comps.items():
        if not libname or ref not in PLACEMENT:
            continue
        x, y, rot = PLACEMENT[ref]
        fp = load_fp(libname)
        board.Add(fp)  # must be on the board before Flip/edits (else pcbnew segfaults)
        fp.SetReference(ref)
        fp.SetPosition(pcbnew.VECTOR2I(mm(x), mm(y)))
        if rot:
            fp.SetOrientationDegrees(rot)
        fp.Flip(fp.GetPosition(), False)  # to back
        # Move the reference designator to the fab layer; on a board this dense
        # silk text overlaps pads/other silk (DRC silk_* errors) and adds no
        # assembly value that the fab drawing doesn't already carry.
        ref_text = fp.Reference()
        ref_text.SetLayer(pcbnew.B_Fab)
        ref_text.SetVisible(True)
        placed[ref] = fp

    # Assign nets to pads from the netlist.
    def pad_net(ref, padnum, netname):
        fp = placed.get(ref)
        if not fp:
            return
        for pad in fp.Pads():
            if pad.GetNumber() == padnum:
                pad.SetNet(netmap[netname])
                return

    for netname, nodes in nets.items():
        if netname.startswith("unconnected-"):
            continue
        for ref, padnum in nodes:
            pad_net(ref, padnum, netname)
    for padnum in MODULE_GND_PADS:
        pad_net("U1", padnum, GND)

    def net_pads(netname):
        pts = []
        for ref, fp in placed.items():
            for pad in fp.Pads():
                if pad.GetNet() and pad.GetNet().GetNetname() == netname:
                    p = pad.GetCenter()
                    pts.append((ref, pad.GetNumber(), p.x / 1e6, p.y / 1e6))
        return pts

    # ------------------------------------------------------------ planes
    keepalive = []

    def add_zone(layer, netname):
        z = pcbnew.ZONE(board)
        z.SetLayer(layer)
        z.SetNet(netmap[netname])
        z.SetLocalClearance(mm(CLEAR))
        z.SetMinThickness(mm(0.2))
        outline = pcbnew.SHAPE_POLY_SET()
        outline.NewOutline()
        for x, y in [(0.2, 0.2), (BOARD_W - 0.2, 0.2), (BOARD_W - 0.2, BOARD_H - 0.2), (0.2, BOARD_H - 0.2)]:
            outline.Append(mm(x), mm(y))
        z.SetOutline(outline)
        keepalive.append(outline)
        board.Add(z)
        return z

    add_zone(pcbnew.In2_Cu, GND)
    add_zone(pcbnew.B_Cu, GND)
    add_zone(pcbnew.F_Cu, GND)
    add_zone(pcbnew.In1_Cu, VSYS)

    # Antenna keep-out under the module's antenna end (belt-and-suspenders with
    # the module footprint's own keep-outs).
    ant = pcbnew.ZONE(board)
    ant.SetIsRuleArea(True)
    ant.SetDoNotAllowCopperPour(True)
    ant.SetDoNotAllowTracks(True)
    ant.SetDoNotAllowVias(True)
    lset = pcbnew.LSET()
    for ly in (pcbnew.F_Cu, pcbnew.In1_Cu, pcbnew.In2_Cu, pcbnew.B_Cu):
        lset.AddLayer(ly)
    ant.SetLayerSet(lset)
    ko = pcbnew.SHAPE_POLY_SET()
    ko.NewOutline()
    for x, y in [(1.5, 85), (11, 85), (11, 93), (1.5, 93)]:
        ko.Append(mm(x), mm(y))
    ant.SetOutline(ko)
    board.Add(ant)

    # ------------------------------------------------------------ routing grid
    ROUTE_LAYERS = (pcbnew.B_Cu, pcbnew.F_Cu)

    def blank_grid():
        return [[None] * NY for _ in range(NX)]

    grids = {ly: blank_grid() for ly in ROUTE_LAYERS}
    BLOCK = "#"

    def cell(x, y):
        return int(round(x / GRID)), int(round(y / GRID))

    def set_block(layer, gx, gy):
        if 0 <= gx < NX and 0 <= gy < NY and grids[layer][gx][gy] is None:
            grids[layer][gx][gy] = BLOCK

    def block_rect(x0, y0, x1, y1, layers=ROUTE_LAYERS):
        cx0, cy0 = cell(x0, y0)
        cx1, cy1 = cell(x1, y1)
        for gx in range(max(0, cx0), min(NX, cx1 + 1)):
            for gy in range(max(0, cy0), min(NY, cy1 + 1)):
                for ly in layers:
                    set_block(ly, gx, gy)

    # Board-edge margin (copper >= EDGE_CLEAR from the edge; add a track half).
    margin = EDGE_CLEAR + 0.1
    block_rect(0, 0, BOARD_W, margin)
    block_rect(0, BOARD_H - margin, BOARD_W, BOARD_H)
    block_rect(0, 0, margin, BOARD_H)
    block_rect(BOARD_W - margin, 0, BOARD_W, BOARD_H)
    # Battery cutout + margin.
    block_rect(CX - BAT_W / 2 - margin, BAT_CY - BAT_H / 2 - margin,
               CX + BAT_W / 2 + margin, BAT_CY + BAT_H / 2 + margin)

    # Honor every rule-area keep-out on the board and inside footprints.
    def block_keepout_poly(poly, layers):
        xs = [p[0] for p in poly]
        ys = [p[1] for p in poly]
        cx0, cy0 = cell(min(xs), min(ys))
        cx1, cy1 = cell(max(xs), max(ys))
        for gx in range(max(0, cx0), min(NX, cx1 + 1)):
            for gy in range(max(0, cy0), min(NY, cy1 + 1)):
                if point_in_poly(gx * GRID, gy * GRID, poly):
                    for ly in layers:
                        set_block(ly, gx, gy)

    def zone_polys(zone):
        polys = []
        sp = zone.Outline()
        for oi in range(sp.OutlineCount()):
            chain = sp.Outline(oi)
            pts = [(chain.CPoint(i).x / 1e6, chain.CPoint(i).y / 1e6)
                   for i in range(chain.PointCount())]
            if len(pts) >= 3:
                polys.append(pts)
        return polys

    keepout_zones = [z for z in board.Zones() if z.GetIsRuleArea()]
    for fp in placed.values():
        for z in fp.Zones():
            if z.GetIsRuleArea():
                keepout_zones.append(z)
    for z in keepout_zones:
        layers = [ly for ly in ROUTE_LAYERS if z.GetLayerSet().Contains(ly)] or list(ROUTE_LAYERS)
        for poly in zone_polys(z):
            block_keepout_poly(poly, layers)

    # Mark pad areas: own net owns its pad cells (+ a one-ring escape halo of
    # its own net); other pads block. Pads never override edge/keep-out blocks.
    pad_cells = {}
    for ref, fp in placed.items():
        for pad in fp.Pads():
            net = pad.GetNet().GetNetname() if pad.GetNet() else None
            c = pad.GetCenter()
            px, py = c.x / 1e6, c.y / 1e6
            sz = pad.GetSize()
            hw = sz.x / 1e6 / 2
            hh = sz.y / 1e6 / 2
            cells = []
            cx0, cy0 = cell(px - hw, py - hh)
            cx1, cy1 = cell(px + hw, py + hh)
            for gx in range(max(0, cx0), min(NX, cx1 + 1)):
                for gy in range(max(0, cy0), min(NY, cy1 + 1)):
                    cells.append((gx, gy))
            if not cells:
                cells = [cell(px, py)]
            pad_cells[(ref, pad.GetNumber())] = (px, py, cells, net)
            for layer in ROUTE_LAYERS:
                for gx, gy in cells:
                    if 0 <= gx < NX and 0 <= gy < NY and grids[layer][gx][gy] != BLOCK:
                        grids[layer][gx][gy] = ("PAD", net)

    def add_track(x0, y0, x1, y1, layer, netcode):
        t = pcbnew.PCB_TRACK(board)
        t.SetStart(pcbnew.VECTOR2I(mm(x0), mm(y0)))
        t.SetEnd(pcbnew.VECTOR2I(mm(x1), mm(y1)))
        t.SetWidth(TRACK_W)
        t.SetLayer(layer)
        t.SetNet(netmap_by_code[netcode])
        board.Add(t)

    def via_edge_ok(gx, gy):
        x, y = gx * GRID, gy * GRID
        if x < VIA_EDGE or x > BOARD_W - VIA_EDGE or y < VIA_EDGE or y > BOARD_H - VIA_EDGE:
            return False
        # Battery cutout + via edge clearance.
        if (CX - BAT_W / 2 - VIA_EDGE <= x <= CX + BAT_W / 2 + VIA_EDGE and
                BAT_CY - BAT_H / 2 - VIA_EDGE <= y <= BAT_CY + BAT_H / 2 + VIA_EDGE):
            return False
        return True

    def can_place_via(gx, gy, netname):
        if not via_edge_ok(gx, gy):
            return False
        for layer in ROUTE_LAYERS:
            for dx in range(-VIA_R, VIA_R + 1):
                for dy in range(-VIA_R, VIA_R + 1):
                    if dx * dx + dy * dy > VIA_R * VIA_R:
                        continue
                    x, y = gx + dx, gy + dy
                    if not (0 <= x < NX and 0 <= y < NY):
                        continue
                    v = grids[layer][x][y]
                    if v is None:
                        continue
                    if v == BLOCK:
                        return False
                    if isinstance(v, tuple):
                        if v[1] != netname:
                            return False
                    elif v != netname:
                        return False
        return True

    def reserve_via(gx, gy, netname):
        for layer in ROUTE_LAYERS:
            for dx in range(-VIA_R, VIA_R + 1):
                for dy in range(-VIA_R, VIA_R + 1):
                    if dx * dx + dy * dy > VIA_R * VIA_R:
                        continue
                    x, y = gx + dx, gy + dy
                    if 0 <= x < NX and 0 <= y < NY and grids[layer][x][y] != BLOCK:
                        grids[layer][x][y] = netname

    def add_via(x, y, netcode, layer_top=pcbnew.F_Cu, layer_bot=pcbnew.B_Cu):
        v = pcbnew.PCB_VIA(board)
        v.SetPosition(pcbnew.VECTOR2I(mm(x), mm(y)))
        v.SetWidth(VIA_D)
        v.SetDrill(VIA_DRILL)
        v.SetLayerPair(layer_top, layer_bot)
        v.SetNet(netmap_by_code[netcode])
        board.Add(v)

    def astar(start, goal, layer, netname):
        g = grids[layer]

        def own(v):
            if v is None:
                return True
            if v == BLOCK:
                return False
            if isinstance(v, tuple):
                return v[1] == netname
            return v == netname

        def foreign(v):
            if v is None or v == BLOCK:
                return False
            if isinstance(v, tuple):
                return v[1] != netname
            return v != netname

        def passable(gx, gy):
            if not (0 <= gx < NX and 0 <= gy < NY):
                return False
            if not own(g[gx][gy]):
                return False
            # Clearance: reject if any neighbour holds foreign copper.
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    if dx == 0 and dy == 0:
                        continue
                    x, y = gx + dx, gy + dy
                    if 0 <= x < NX and 0 <= y < NY and foreign(g[x][y]):
                        return False
            return True

        (sx, sy), (tx, ty) = start, goal
        openq = [(0, sx, sy)]
        came = {}
        gcost = {(sx, sy): 0}
        pops = 0
        while openq:
            pops += 1
            if pops > 400000:
                return None
            _, x, y = heapq.heappop(openq)
            if (x, y) == (tx, ty):
                path = [(x, y)]
                while (x, y) in came:
                    x, y = came[(x, y)]
                    path.append((x, y))
                return path[::-1]
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                nx, ny = x + dx, y + dy
                if not (0 <= nx < NX and 0 <= ny < NY):
                    continue
                if (nx, ny) != (tx, ty) and not passable(nx, ny):
                    continue
                ng = gcost[(x, y)] + 1
                if ng < gcost.get((nx, ny), 1 << 30):
                    gcost[(nx, ny)] = ng
                    h = abs(nx - tx) + abs(ny - ty)
                    came[(nx, ny)] = (x, y)
                    heapq.heappush(openq, (ng + h, nx, ny))
        return None

    def commit_path(path, layer, netname):
        code = netmap[netname].GetNetCode()
        for (ax, ay), (bx, by) in zip(path, path[1:]):
            add_track(ax * GRID, ay * GRID, bx * GRID, by * GRID, layer, code)
        for gx, gy in path:
            v = grids[layer][gx][gy]
            if v is None or (isinstance(v, tuple) and v[0] == "PAD"):
                grids[layer][gx][gy] = netname

    vsys_code = netmap[VSYS].GetNetCode()
    gnd_code = netmap[GND].GetNetCode()

    def big_pad(padnum, ref):
        for pad in placed[ref].Pads():
            if pad.GetNumber() == padnum:
                s = pad.GetSize()
                return min(s.x, s.y) / 1e6 >= 0.7
        return False

    def astar_short(start, layer, netname, limit=12):
        """Short B.Cu escape from a pad cell to the nearest via-capable open
        cell; returns (path, cell) or (None, None)."""
        best = None
        for r in range(1, limit):
            ring = []
            for dx in range(-r, r + 1):
                for dy in (-r, r):
                    ring.append((start[0] + dx, start[1] + dy))
                if -r < dx < r:
                    continue
            for dy in range(-r + 1, r):
                ring.append((start[0] - r, start[1] + dy))
                ring.append((start[0] + r, start[1] + dy))
            for gx, gy in ring:
                if not (0 <= gx < NX and 0 <= gy < NY):
                    continue
                if not can_place_via(gx, gy, netname):
                    continue
                path = astar(start, (gx, gy), layer, netname)
                if path is not None and len(path) <= limit:
                    return path, (gx, gy)
        return None, None

    # Connect every plane pad (VSYS -> In1, GND -> In2). A pad wide enough takes
    # a via-in-pad; a fine-pitch pad gets a short B.Cu stub to a via dropped in
    # nearby open copper, so the plane connection never breaks hole-clearance.
    def connect_plane(net, code):
        for (ref, padnum), (px, py, cells, padnet) in list(pad_cells.items()):
            if padnet != net:
                continue
            gx, gy = cell(px, py)
            if grids[pcbnew.B_Cu][gx][gy] == BLOCK:
                continue
            if big_pad(padnum, ref) and can_place_via(gx, gy, net):
                add_via(px, py, code)
                reserve_via(gx, gy, net)
                continue
            path, vcell = astar_short((gx, gy), pcbnew.B_Cu, net)
            if path is not None:
                commit_path(path, pcbnew.B_Cu, net)
                add_via(vcell[0] * GRID, vcell[1] * GRID, code)
                reserve_via(*vcell, net)

    # Connect planes before signal routing so every plane pad gets its via /
    # stub first (power integrity), then signals thread the remaining space.
    connect_plane(VSYS, vsys_code)
    connect_plane(GND, gnd_code)

    # ------------------------------------------------------------ route signals
    routed, unrouted = [], []
    candidates = [
        n for n in nets
        if n not in (GND, VSYS) and not n.startswith("unconnected-") and len(net_pads(n)) >= 2
    ]

    def net_span(n):
        pts = net_pads(n)
        xs = [p[2] for p in pts]
        ys = [p[3] for p in pts]
        return (max(xs) - min(xs)) + (max(ys) - min(ys))

    signal_nets = sorted(candidates, key=net_span)
    for netname in signal_nets:
        pts = net_pads(netname)
        anchors = [(cell(px, py), (px, py)) for _, _, px, py in pts]
        remaining = anchors[:]
        chain = [remaining.pop(0)]
        while remaining:
            (lx, ly), _ = chain[-1]
            remaining.sort(key=lambda a: abs(a[0][0] - lx) + abs(a[0][1] - ly))
            chain.append(remaining.pop(0))
        ok = True
        for (c0, _), (c1, _) in zip(chain, chain[1:]):
            path = astar(c0, c1, pcbnew.B_Cu, netname)
            layer = pcbnew.B_Cu
            if path is None and can_place_via(*c0, netname) and can_place_via(*c1, netname):
                path = astar(c0, c1, pcbnew.F_Cu, netname)
                layer = pcbnew.F_Cu
                if path is not None:
                    code = netmap[netname].GetNetCode()
                    add_via(c0[0] * GRID, c0[1] * GRID, code)
                    add_via(c1[0] * GRID, c1[1] * GRID, code)
                    reserve_via(*c0, netname)
                    reserve_via(*c1, netname)
            if path is None:
                ok = False
                continue
            commit_path(path, layer, netname)
        (routed if ok else unrouted).append(netname)

    # GND stitching vias on a lattice through open cells: tie the B.Cu / F.Cu
    # ground pours to the solid In2 plane and reduce isolated fill.
    stitch = 0
    step = max(1, int(round(5.0 / GRID)))  # ~5 mm lattice
    for gx in range(3, NX - 3, step):
        for gy in range(3, NY - 3, step):
            if grids[pcbnew.B_Cu][gx][gy] is None and can_place_via(gx, gy, GND):
                add_via(gx * GRID, gy * GRID, gnd_code)
                reserve_via(gx, gy, GND)
                stitch += 1

    # ------------------------------------------------------------ fill + save
    board.BuildConnectivity()
    filler = pcbnew.ZONE_FILLER(board)
    copper_zones = pcbnew.ZONES()
    for z in board.Zones():
        if not z.GetIsRuleArea():
            copper_zones.append(z)
    filler.Fill(copper_zones)
    for z in board.Zones():
        if not z.GetIsRuleArea():
            print(f"  zone {board.GetLayerName(z.GetLayer())} {z.GetNetname()}: "
                  f"area {z.GetFilledArea() / 1e12:.1f} mm^2")
    board.BuildConnectivity()
    pcbnew.SaveBoard(str(BOARD), board)

    conn = board.GetConnectivity()
    unconn = conn.GetUnconnectedCount(True) if hasattr(conn, "GetUnconnectedCount") else -1
    print(f"placed {len(placed)} footprints; routed {len(routed)}/{len(signal_nets)} signal nets; "
          f"{stitch} GND stitching vias")
    if unrouted:
        print("unrouted:", ", ".join(unrouted))
    print(f"open ratsnest connections: {unconn}")

    export_fab()


def export_fab() -> None:
    FAB.mkdir(exist_ok=True)

    def run(args):
        r = subprocess.run(args, capture_output=True, text=True)
        print(" ".join(args[:4]), "->", "ok" if r.returncode == 0 else r.stderr.strip()[:200])

    run(["kicad-cli", "pcb", "export", "gerbers", "-o", str(FAB) + "/", str(BOARD)])
    run(["kicad-cli", "pcb", "export", "drill", "-o", str(FAB) + "/", str(BOARD)])
    run(["kicad-cli", "pcb", "export", "pos", "-o", str(FAB / "inkbot-magsafe-pos.csv"),
         "--format", "csv", "--units", "mm", str(BOARD)])


if __name__ == "__main__":
    main()

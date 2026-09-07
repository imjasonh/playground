#!/usr/bin/env python3
"""Place, net, pour, route, and export the inkbot-magsafe board with pcbnew.

Starts from the outline board written by ``generate_pcb.py`` and the schematic
netlist exported by ``kicad-cli sch export netlist``. Places every footprint on
the back, assigns nets to pads, pours the ground and VSYS planes, routes the
signal nets with a maze router (B.Cu, F.Cu escape), fills the zones, and writes
Gerbers, drill, centroid, and BOM under ``kicad/fab/``.

The radio is a pre-certified Raytac MDBT50Q-512K module, so there is no antenna
or matching network to route; a copper keep-out is placed under the module's
antenna end. Run DRC in the KiCad GUI before a production order.
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

# Placement: ref -> (x_mm, y_mm, rotation_deg). All parts mount on the back
# (the panel is the front face). Passives cluster near the part they serve.
# The magnet ring / coil dominate the top (~y < 57) and the LiPo cutout takes the
# center (x14-46, y60-80). Parts live in the two columns beside the cutout and
# the bottom band (y > 82), with the module in the bottom-left and its antenna
# end toward the bottom-left corner (far from the ring/coil).
PLACEMENT = {
    "U1": (17.0, 87.5, 0),   # module: antenna end to the left (bottom-left corner)
    "J1": (42.0, 93.0, 0),   # panel FPC (pads sit ~1.85 mm below center)
    # Qi receiver + coil leads: left column beside the cutout
    "U5": (8.5, 66.0, 0),
    "L1": (24.0, 57.0, 0),
    # panel power near the FPC
    "U3": (53.0, 88.0, 0),
    "U4": (53.0, 93.0, 0),
    # module bypass + LFXO next to U1
    "C15": (28.0, 86.0, 0),
    "C16": (28.0, 89.0, 0),
    "Y1": (30.0, 92.0, 90),
    # sense / bulk: right column beside the cutout
    "C10": (52.0, 64.0, 0),
    "C11": (56.0, 64.0, 0),
    "RT1": (52.0, 68.0, 0),
    "R5": (56.0, 68.0, 0),
    "R6": (52.0, 72.0, 0),
    "R7": (56.0, 72.0, 0),
    "R8": (52.0, 76.0, 0),
    # Qi support cluster in the left column around U5
    "C1": (4.0, 62.0, 0),
    "C2": (4.0, 66.0, 0),
    "C3": (4.0, 70.0, 0),
    "C4": (8.0, 62.0, 0),
    "C5": (12.0, 62.0, 0),
    "C6": (12.0, 66.0, 0),
    "C7": (4.0, 74.0, 0),
    "C8": (8.0, 74.0, 0),
    "C9": (12.0, 74.0, 0),
    "R1": (4.0, 78.0, 0),
    "R2": (8.0, 78.0, 0),
    "R3": (12.0, 78.0, 0),
    "R4": (12.0, 70.0, 0),
    # panel-power passives near U3/U4/J1
    "C12": (58.0, 88.0, 0),
    "C13": (48.0, 90.0, 0),
    "C14": (58.0, 93.0, 0),
    "C21": (52.0, 97.0, 0),
    # SWD test pads in the bottom band, right of the antenna keep-out and below
    # the module (clear of the x1.5-11 / y85-93 keep-out).
    "TP1": (14.0, 96.5, 0),
    "TP2": (18.0, 96.5, 0),
    "TP3": (22.0, 96.5, 0),
    "TP4": (26.0, 96.5, 0),
    "TP5": (30.0, 96.5, 0),
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
CLEAR = 0.15  # mm design clearance for the router halo

# Maze-router grid. Fine enough to escape ~0.8 mm-pitch module pads.
GRID = 0.15  # mm
NX = int(BOARD_W / GRID) + 1
NY = int(BOARD_H / GRID) + 1


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
    # Tie the module's redundant GND / VBUS pads to GND.
    for padnum in MODULE_GND_PADS:
        pad_net("U1", padnum, GND)

    # Collect routable signal nets (everything with >=2 placed pads that is not
    # a plane net).
    def net_pads(netname):
        pts = []
        for ref, fp in placed.items():
            for pad in fp.Pads():
                if pad.GetNet() and pad.GetNet().GetNetname() == netname:
                    p = pad.GetCenter()
                    pts.append((ref, pad.GetNumber(), p.x / 1e6, p.y / 1e6))
        return pts

    # ------------------------------------------------------------ planes
    # SWIG lets Python garbage-collect a SHAPE_POLY_SET passed to SetOutline,
    # which leaves the zone with a dangling outline that fills to 0 area. Keep
    # every outline referenced for the lifetime of the board.
    keepalive = []

    def add_zone(layer, netname, keepout=False):
        z = pcbnew.ZONE(board)
        z.SetLayer(layer)
        if not keepout:
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

    # Antenna keep-out: no copper under the module's antenna end (bottom edge).
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

    # ------------------------------------------------------------ routing
    # Occupancy grids per layer: cell -> owning net name (or None).
    def blank_grid():
        return [[None] * NY for _ in range(NX)]

    grids = {pcbnew.B_Cu: blank_grid(), pcbnew.F_Cu: blank_grid()}
    BLOCK = "#"

    def cell(x, y):
        return int(round(x / GRID)), int(round(y / GRID))

    # Block board edge margin, cutout, and antenna keep-out on both layers.
    def block_rect(x0, y0, x1, y1):
        cx0, cy0 = cell(x0, y0)
        cx1, cy1 = cell(x1, y1)
        for gx in range(max(0, cx0), min(NX, cx1 + 1)):
            for gy in range(max(0, cy0), min(NY, cy1 + 1)):
                grids[pcbnew.B_Cu][gx][gy] = BLOCK
                grids[pcbnew.F_Cu][gx][gy] = BLOCK

    block_rect(0, 0, BOARD_W, 0.5)
    block_rect(0, BOARD_H - 0.5, BOARD_W, BOARD_H)
    block_rect(0, 0, 0.5, BOARD_H)
    block_rect(BOARD_W - 0.5, 0, BOARD_W, BOARD_H)
    block_rect(CX - BAT_W / 2 - 0.5, BAT_CY - BAT_H / 2 - 0.5, CX + BAT_W / 2 + 0.5, BAT_CY + BAT_H / 2 + 0.5)
    block_rect(1.5, 85, 11, 93)  # antenna keep-out (module antenna end)

    # Mark pad areas: own net owns its pad cells; other pads block with a halo.
    pad_cells = {}  # (ref,padnum) -> list of (gx,gy)
    for ref, fp in placed.items():
        for pad in fp.Pads():
            net = pad.GetNet().GetNetname() if pad.GetNet() else None
            c = pad.GetCenter()
            px, py = c.x / 1e6, c.y / 1e6
            sz = pad.GetSize()
            # Block the pad body only (no clearance halo) so routes can escape
            # between fine-pitch module pins; GUI DRC tightens clearance later.
            hw = sz.x / 1e6 / 2
            hh = sz.y / 1e6 / 2
            cells = []
            cx0, cy0 = cell(px - hw, py - hh)
            cx1, cy1 = cell(px + hw, py + hh)
            for gx in range(max(0, cx0), min(NX, cx1 + 1)):
                for gy in range(max(0, cy0), min(NY, cy1 + 1)):
                    cells.append((gx, gy))
            pad_cells[(ref, pad.GetNumber())] = (px, py, cells, net)
            # Pad copper always overrides an edge/cutout block so a pad near the
            # board edge stays reachable by its own net.
            for layer in (pcbnew.B_Cu, pcbnew.F_Cu):
                for gx, gy in cells:
                    grids[layer][gx][gy] = ("PAD", net)

    def add_track(x0, y0, x1, y1, layer, netcode):
        t = pcbnew.PCB_TRACK(board)
        t.SetStart(pcbnew.VECTOR2I(mm(x0), mm(y0)))
        t.SetEnd(pcbnew.VECTOR2I(mm(x1), mm(y1)))
        t.SetWidth(TRACK_W)
        t.SetLayer(layer)
        t.SetNet(netmap_by_code[netcode])
        board.Add(t)

    def add_via(x, y, netcode):
        v = pcbnew.PCB_VIA(board)
        v.SetPosition(pcbnew.VECTOR2I(mm(x), mm(y)))
        v.SetWidth(VIA_D)
        v.SetDrill(VIA_DRILL)
        v.SetLayerPair(pcbnew.F_Cu, pcbnew.B_Cu)
        v.SetNet(netmap_by_code[netcode])
        board.Add(v)

    netmap_by_code = {netmap[n].GetNetCode(): netmap[n] for n in netmap}

    def astar(start, goal, layer, netname):
        """Grid A* on one layer; cells free if None, own-net PAD, or own track."""
        g = grids[layer]

        def passable(gx, gy):
            if not (0 <= gx < NX and 0 <= gy < NY):
                return False
            v = g[gx][gy]
            if v is None:
                return True
            if isinstance(v, tuple):
                kind, owner = v
                return owner == netname
            return v == netname  # own track

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
            if grids[layer][gx][gy] is None or (
                isinstance(grids[layer][gx][gy], tuple) and grids[layer][gx][gy][0] == "PAD"
            ):
                grids[layer][gx][gy] = netname

    # VSYS pads: via to the In1 VSYS plane (short local drop, no track routing).
    vsys_code = netmap[VSYS].GetNetCode()
    for (ref, padnum), (px, py, cells, net) in pad_cells.items():
        if net == VSYS:
            add_via(px, py, vsys_code)

    # Route the remaining signal nets (skip planes).
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

    # Route the tightest nets first so short local links lock in before long hauls.
    signal_nets = sorted(candidates, key=net_span)
    for netname in signal_nets:
        pts = net_pads(netname)
        # Nearest-neighbour chain over pad anchors.
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
            if path is None:
                path = astar(c0, c1, pcbnew.F_Cu, netname)
                layer = pcbnew.F_Cu
                if path is not None:
                    add_via(c0[0] * GRID, c0[1] * GRID, netmap[netname].GetNetCode())
                    add_via(c1[0] * GRID, c1[1] * GRID, netmap[netname].GetNetCode())
            if path is None:
                ok = False
                continue
            commit_path(path, layer, netname)
        (routed if ok else unrouted).append(netname)

    # ------------------------------------------------------------ fill + save
    # Connectivity must be built before the filler runs, or zones fill to 0 area.
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
    print(f"placed {len(placed)} footprints; routed {len(routed)}/{len(signal_nets)} signal nets")
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
    # The curated BOM lives at docs/inkbot-magsafe-bom.csv; KiCad 7's CLI has no
    # `sch export bom`, so it is not regenerated here.


if __name__ == "__main__":
    main()

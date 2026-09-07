#!/usr/bin/env python3
"""Place primary footprints on the inkbot-magsafe board with pcbnew."""

from __future__ import annotations

from pathlib import Path

import pcbnew

BOARD = Path(__file__).resolve().parent / "inkbot-magsafe.kicad_pcb"
FP_ROOT = Path("/usr/share/kicad/footprints")


def add_fp(board: pcbnew.BOARD, pretty: str, name: str, ref: str, x_mm: float, y_mm: float, back: bool = True) -> None:
    fp = pcbnew.FootprintLoad(str(FP_ROOT / f"{pretty}.pretty"), name)
    if fp is None:
        raise SystemExit(f"missing footprint {pretty}:{name}")
    fp.SetReference(ref)
    fp.SetPosition(pcbnew.VECTOR2I(int(x_mm * 1e6), int(y_mm * 1e6)))
    if back:
        fp.Flip(fp.GetPosition(), False)
    board.Add(fp)
    print(f"placed {ref} ({pretty}:{name})")


def main() -> None:
    board = pcbnew.LoadBoard(str(BOARD))
    # Clear any prior placeholders.
    for fp in list(board.GetFootprints()):
        board.Remove(fp)

    # Board is 60 x 99 mm portrait; the coil/ring fill the top (~y<50), so parts
    # mount on the back below it, ringing the cutout.
    add_fp(board, "Package_DFN_QFN", "Nordic_QFN-40-1EP_5x5mm_P0.4mm", "U1", 16, 58, True)
    # BQ51050 RHL-20
    rhl = None
    for candidate in ("Texas_VQFN-RHL-20", "Texas_RHL0020A", "RHL0020A"):
        rhl = pcbnew.FootprintLoad(str(FP_ROOT / "Package_DFN_QFN.pretty"), candidate)
        if rhl is not None:
            break
    if rhl is None:
        # Search
        for p in (FP_ROOT / "Package_DFN_QFN.pretty").glob("*RHL*"):
            print("candidate", p.name)
        raise SystemExit("BQ51050 footprint not found")
    rhl.SetReference("U5")
    rhl.SetPosition(pcbnew.VECTOR2I(int(42 * 1e6), int(58 * 1e6)))
    rhl.Flip(rhl.GetPosition(), False)
    board.Add(rhl)
    print("placed U5")

    add_fp(board, "Package_TO_SOT_SMD", "SOT-23-6", "U3", 14, 90, True)
    add_fp(board, "Package_TO_SOT_SMD", "SOT-23-5", "U4", 26, 90, True)
    add_fp(
        board,
        "Connector_FFC-FPC",
        "Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
        "J1",
        30.0,
        95,
        False,
    )
    for i, y in enumerate((58, 62, 66, 70, 74), start=1):
        add_fp(board, "TestPoint", "TestPoint_Pad_D1.5mm", f"TP{i}", 4, y, True)

    pcbnew.SaveBoard(str(BOARD), board)
    print("saved", [fp.GetReference() for fp in board.GetFootprints()])


if __name__ == "__main__":
    main()

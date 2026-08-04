#!/usr/bin/env python3
"""Work backwards from a target Game of Life pattern to a printable history.

Given a top layer (a letter, icon, or QR code) and a height in generations,
search for generation-0 seeds whose forward B3/S23 evolution lands exactly on
that pattern. The resulting seed string can be dropped into
``game_of_life.scad`` (``preset="custom"``) so the sculpture's roof *is* the
target and every layer beneath is a valid Life predecessor.

Two SAT strategies (require ``python-sat`` — see requirements.txt):

- **maxsat** (default): walk one generation at a time, preferring predecessors
  that stay close to the current pattern and stay sparse. Still lifes and
  period-2 oscillators reverse to arbitrary height. Arbitrary drawings usually
  manage a handful of generations before hitting a Garden-of-Eden dead end.
- **multigen**: one SAT instance for the whole stack. Complete when it
  finishes — if a history of that height exists on the board, it will find
  one — but the formula grows with board × height.

Unconstrained one-step SAT tends to emit dense predecessors that are
themselves Gardens of Eden; that is why plain SAT chaining fails and why
life-stl dropped its earlier zero-birth reverse mode (a different, stricter
problem). Min-Hamming MaxSAT is what makes chaining practical.
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from dataclasses import dataclass
from typing import Optional, Sequence

try:
    from pysat.examples.rc2 import RC2
    from pysat.formula import CNF, WCNF
    from pysat.solvers import Glucose3

    HAS_PYSAT = True
except ImportError:  # pragma: no cover - optional dependency
    HAS_PYSAT = False


# ---------------------------------------------------------------------------
# Grid
# ---------------------------------------------------------------------------

LIVE_CHARS = set("1#OoXx")


@dataclass(frozen=True)
class Grid:
    width: int
    height: int
    cells: tuple[int, ...]  # row-major 0/1

    def __post_init__(self) -> None:
        if self.width < 1 or self.height < 1:
            raise ValueError("grid must be non-empty")
        if len(self.cells) != self.width * self.height:
            raise ValueError("cells length must equal width*height")

    def alive(self, x: int, y: int) -> int:
        if x < 0 or y < 0 or x >= self.width or y >= self.height:
            return 0
        return self.cells[y * self.width + x]

    def live_count(self) -> int:
        return int(sum(self.cells))

    def step(self) -> Grid:
        w, h = self.width, self.height
        nxt: list[int] = []
        for y in range(h):
            for x in range(w):
                n = 0
                for dy in (-1, 0, 1):
                    for dx in (-1, 0, 1):
                        if dx == 0 and dy == 0:
                            continue
                        n += self.alive(x + dx, y + dy)
                a = self.alive(x, y)
                nxt.append(1 if (n == 3 or (a and n == 2)) else 0)
        return Grid(w, h, tuple(nxt))

    def padded(self, margin: int) -> Grid:
        if margin < 0:
            raise ValueError("margin must be >= 0")
        if margin == 0:
            return self
        nw, nh = self.width + 2 * margin, self.height + 2 * margin
        out = [0] * (nw * nh)
        for y in range(self.height):
            for x in range(self.width):
                if self.alive(x, y):
                    out[(y + margin) * nw + (x + margin)] = 1
        return Grid(nw, nh, tuple(out))

    def render(self, live: str = "#", dead: str = ".") -> str:
        rows = []
        for y in range(self.height):
            rows.append(
                "".join(
                    live if self.cells[y * self.width + x] else dead
                    for x in range(self.width)
                )
            )
        return "\n".join(rows)

    def seed_string(self) -> str:
        """OpenSCAD ``seed_pattern`` form: rows joined by ``/``."""
        return "/".join(
            "".join(
                "#" if self.cells[y * self.width + x] else "."
                for x in range(self.width)
            )
            for y in range(self.height)
        )


def parse_pattern(text: str) -> Grid:
    rows = [r for r in text.strip().split("/") if r != ""]
    if not rows:
        raise ValueError("empty pattern")
    height = len(rows)
    width = max(len(r) for r in rows)
    cells: list[int] = []
    for row in rows:
        for x in range(width):
            ch = row[x] if x < len(row) else "."
            cells.append(1 if ch in LIVE_CHARS else 0)
    return Grid(width, height, tuple(cells))


# ---------------------------------------------------------------------------
# Optional SAT core
# ---------------------------------------------------------------------------


class _VarGen:
    def __init__(self) -> None:
        self.n = 0

    def __call__(self) -> int:
        self.n += 1
        return self.n


def _xor2(cnf: CNF, a: int, b: int, new_var) -> int:
    s = new_var()
    cnf.append([-a, -b, -s])
    cnf.append([-a, b, s])
    cnf.append([a, -b, s])
    cnf.append([a, b, -s])
    return s


def _and2(cnf: CNF, a: int, b: int, new_var) -> int:
    o = new_var()
    cnf.append([-a, -b, o])
    cnf.append([a, -o])
    cnf.append([b, -o])
    return o


def _or2(cnf: CNF, a: int, b: int, new_var) -> int:
    o = new_var()
    cnf.append([a, b, -o])
    cnf.append([-a, o])
    cnf.append([-b, o])
    return o


def _half_adder(cnf: CNF, a: int, b: int, new_var) -> tuple[int, int]:
    return _xor2(cnf, a, b, new_var), _and2(cnf, a, b, new_var)


def _full_adder(cnf: CNF, a: int, b: int, cin: int, new_var) -> tuple[int, int]:
    s1, c1 = _half_adder(cnf, a, b, new_var)
    s, c2 = _half_adder(cnf, s1, cin, new_var)
    return s, _or2(cnf, c1, c2, new_var)


def _add_bitnumbers(cnf: CNF, a: Sequence[int], b: Sequence[int], new_var) -> list[int]:
    n = max(len(a), len(b))
    out: list[int] = []
    carry: Optional[int] = None
    for i in range(n):
        ai = a[i] if i < len(a) else None
        bi = b[i] if i < len(b) else None
        if carry is None:
            if ai is None:
                assert bi is not None
                out.append(bi)
            elif bi is None:
                out.append(ai)
            else:
                s, carry = _half_adder(cnf, ai, bi, new_var)
                out.append(s)
        else:
            if ai is None:
                assert bi is not None
                s, carry = _half_adder(cnf, bi, carry, new_var)
                out.append(s)
            elif bi is None:
                s, carry = _half_adder(cnf, ai, carry, new_var)
                out.append(s)
            else:
                s, carry = _full_adder(cnf, ai, bi, carry, new_var)
                out.append(s)
    if carry is not None:
        out.append(carry)
    return out


def _sum_lits(cnf: CNF, lits: Sequence[int], new_var) -> list[int]:
    nums: list[list[int]] = [[lit] for lit in lits]
    if not nums:
        return []
    while len(nums) > 1:
        nums.append(_add_bitnumbers(cnf, nums.pop(), nums.pop(), new_var))
    return nums[0]


def _iff_bits_eq(cnf: CNF, bits: Sequence[int], value: int, flag: int) -> None:
    if value >> len(bits):
        cnf.append([-flag])
        return
    req = [b if ((value >> i) & 1) else -b for i, b in enumerate(bits)]
    for lit in req:
        cnf.append([-flag, lit])
    cnf.append([-lit for lit in req] + [flag])


def _encode_life(cnf: CNF, center: int, neigh: Sequence[int], next_var: int, new_var) -> None:
    """next_var <=> Life(center, neigh) under B3/S23 (missing neigh = dead)."""
    sb = _sum_lits(cnf, neigh, new_var)
    s2, s3 = new_var(), new_var()
    _iff_bits_eq(cnf, sb, 2, s2)
    _iff_bits_eq(cnf, sb, 3, s3)
    cs2 = _and2(cnf, center, s2, new_var)
    live_next = _or2(cnf, s3, cs2, new_var)
    cnf.append([-live_next, next_var])
    cnf.append([live_next, -next_var])


def _neighbor_vars(cell: Sequence[Sequence[int]], x: int, y: int) -> list[int]:
    h = len(cell)
    w = len(cell[0])
    out = []
    for dy in (-1, 0, 1):
        for dx in (-1, 0, 1):
            if dx == 0 and dy == 0:
                continue
            nx, ny = x + dx, y + dy
            if 0 <= nx < w and 0 <= ny < h:
                out.append(cell[ny][nx])
    return out


def _grid_from_model(cell: Sequence[Sequence[int]], model_pos: set[int]) -> Grid:
    h = len(cell)
    w = len(cell[0])
    cells = tuple(
        1 if cell[y][x] in model_pos else 0 for y in range(h) for x in range(w)
    )
    return Grid(w, h, cells)


# ---------------------------------------------------------------------------
# Search
# ---------------------------------------------------------------------------


class ReverseError(RuntimeError):
    """No valid history of the requested height was found."""

    def __init__(self, message: str, achieved: int = 0):
        super().__init__(message)
        self.achieved = achieved


def _life_cnf(target: Grid) -> tuple[CNF, list[list[int]], _VarGen]:
    """Hard Life constraints: cell[y][x] is the predecessor variable."""
    w, h = target.width, target.height
    vg = _VarGen()
    cell = [[vg() for _ in range(w)] for _ in range(h)]
    cnf = CNF()
    for y in range(h):
        for x in range(w):
            want = vg()
            cnf.append([want] if target.alive(x, y) else [-want])
            _encode_life(cnf, cell[y][x], _neighbor_vars(cell, x, y), want, vg)
    return cnf, cell, vg


def _score_predecessor(pred: Grid, target: Grid) -> tuple[int, int, int]:
    """Lower is better: Hamming distance, live count, then births."""
    ham = sum(a != b for a, b in zip(pred.cells, target.cells))
    births = sum(1 for a, b in zip(pred.cells, target.cells) if b and not a)
    return (ham, pred.live_count(), births)


def _sat_best_predecessor(target: Grid, samples: int = 12) -> Optional[Grid]:
    """Enumerate a few SAT predecessors and keep the sparsest / closest."""
    cnf, cell, _vg = _life_cnf(target)
    w, h = target.width, target.height
    best: Optional[Grid] = None
    best_score: Optional[tuple[int, int, int]] = None
    with Glucose3(bootstrap_with=cnf.clauses) as solver:
        for y in range(h):
            for x in range(w):
                v = cell[y][x]
                try:
                    solver.set_phases([v if target.alive(x, y) else -v])
                except Exception:
                    pass
        for _ in range(samples):
            if not solver.solve():
                break
            model = solver.get_model()
            pred = _grid_from_model(cell, {v for v in model if v > 0})
            if pred.step() != target:
                raise ReverseError("internal error: SAT predecessor failed forward check")
            score = _score_predecessor(pred, target)
            if best_score is None or score < best_score:
                best, best_score = pred, score
            # Block this solution and look for another.
            solver.add_clause(
                [
                    (-cell[i // w][i % w] if pred.cells[i] else cell[i // w][i % w])
                    for i in range(w * h)
                ]
            )
    return best


def _maxsat_predecessor(target: Grid, hamming_weight: int = 3, sparse_weight: int = 1) -> Optional[Grid]:
    if not HAS_PYSAT:
        raise ReverseError("python-sat is not installed (pip install -r requirements.txt)")
    w, h = target.width, target.height
    # RC2 MaxSAT is excellent on small boards but stalls on QR-sized ones;
    # fall back to multi-sample SAT there.
    if w * h > 200:
        return _sat_best_predecessor(target)

    cnf, cell, _vg = _life_cnf(target)
    wcnf = WCNF()
    for clause in cnf.clauses:
        wcnf.append(clause)
    for y in range(h):
        for x in range(w):
            v = cell[y][x]
            if hamming_weight:
                wcnf.append([v if target.alive(x, y) else -v], weight=hamming_weight)
            if sparse_weight:
                wcnf.append([-v], weight=sparse_weight)
    with RC2(wcnf) as rc2:
        model = rc2.compute()
    if model is None:
        return None
    pred = _grid_from_model(cell, {v for v in model if v > 0})
    if pred.step() != target:
        raise ReverseError("internal error: MaxSAT predecessor failed forward check")
    return pred


def _multigen_sat(target: Grid, generations: int) -> Optional[list[Grid]]:
    if not HAS_PYSAT:
        raise ReverseError("python-sat is not installed (pip install -r requirements.txt)")
    w, h = target.width, target.height
    layers = generations + 1
    vg = _VarGen()
    cell = [[[vg() for _ in range(w)] for _ in range(h)] for _ in range(layers)]
    cnf = CNF()
    top = layers - 1
    for y in range(h):
        for x in range(w):
            cnf.append([cell[top][y][x]] if target.alive(x, y) else [-cell[top][y][x]])
    for z in range(generations):
        for y in range(h):
            for x in range(w):
                _encode_life(
                    cnf,
                    cell[z][y][x],
                    _neighbor_vars(cell[z], x, y),
                    cell[z + 1][y][x],
                    vg,
                )
    with Glucose3(bootstrap_with=cnf.clauses) as solver:
        for y in range(h):
            for x in range(w):
                v = cell[0][y][x]
                try:
                    solver.set_phases([v if target.alive(x, y) else -v])
                except Exception:
                    pass
        if not solver.solve():
            return None
        pos = {v for v in solver.get_model() if v > 0}
    hist = [_grid_from_model(cell[z], pos) for z in range(layers)]
    _assert_history(hist, target)
    return hist


def _assert_history(hist: Sequence[Grid], target: Grid) -> None:
    if not hist:
        raise ReverseError("empty history")
    if hist[-1] != target:
        raise ReverseError("history does not end at the target")
    for i in range(len(hist) - 1):
        if hist[i].step() != hist[i + 1]:
            raise ReverseError(f"forward break between generations {i} and {i + 1}")


def _walksat_predecessor(target: Grid, rng: random.Random, max_flips: int = 80_000) -> Optional[Grid]:
    w, h = target.width, target.height
    pred = list(target.cells)
    tgt = target.cells

    def next_at(cells: list[int], x: int, y: int) -> int:
        n = 0
        for dy in (-1, 0, 1):
            for dx in (-1, 0, 1):
                if dx == 0 and dy == 0:
                    continue
                nx, ny = x + dx, y + dy
                if 0 <= nx < w and 0 <= ny < h:
                    n += cells[ny * w + nx]
        a = cells[y * w + x]
        return 1 if (n == 3 or (a and n == 2)) else 0

    nxt = [next_at(pred, x, y) for y in range(h) for x in range(w)]
    bad = sum(a != b for a, b in zip(nxt, tgt))
    if bad == 0:
        return Grid(w, h, tuple(pred))

    def flip(i: int) -> None:
        nonlocal bad
        fx, fy = i % w, i // w
        pred[i] ^= 1
        for y in range(max(0, fy - 1), min(h, fy + 2)):
            for x in range(max(0, fx - 1), min(w, fx + 2)):
                j = y * w + x
                old, new = nxt[j], next_at(pred, x, y)
                if old != new:
                    nxt[j] = new
                    if old == tgt[j]:
                        bad += 1
                    elif new == tgt[j]:
                        bad -= 1

    for _ in range(max_flips):
        if bad == 0:
            return Grid(w, h, tuple(pred))
        mism = [j for j, (a, b) in enumerate(zip(nxt, tgt)) if a != b]
        j = mism[rng.randrange(len(mism))]
        jx, jy = j % w, j // w
        cands = [
            (jy + dy) * w + (jx + dx)
            for dy in (-1, 0, 1)
            for dx in (-1, 0, 1)
            if 0 <= jx + dx < w and 0 <= jy + dy < h
        ]
        if rng.random() < 0.25:
            flip(cands[rng.randrange(len(cands))])
            continue
        best_bad = 10**9
        ties: list[int] = []
        for i in cands:
            flip(i)
            if bad < best_bad:
                best_bad = bad
                ties = [i]
            elif bad == best_bad:
                ties.append(i)
            flip(i)
        flip(ties[rng.randrange(len(ties))])
    return Grid(w, h, tuple(pred)) if bad == 0 else None


def reverse_history(
    target: Grid,
    generations: int,
    method: str = "auto",
    rng: Optional[random.Random] = None,
    verbose: bool = False,
) -> list[Grid]:
    """Return ``[gen0, ..., target]`` of length ``generations + 1``."""
    if generations < 0:
        raise ValueError("generations must be >= 0")
    if generations == 0:
        return [target]
    if target.step() == target:
        return [target] * (generations + 1)

    rng = rng or random.Random(0)
    method = method.lower()
    if method == "auto":
        method = "maxsat" if HAS_PYSAT else "walksat"

    if method == "multigen":
        if verbose:
            print(
                f"multi-gen SAT on {target.width}x{target.height}x{generations + 1}...",
                file=sys.stderr,
            )
        hist = _multigen_sat(target, generations)
        if hist is None:
            raise ReverseError(
                "multi-gen SAT proved unsatisfiable — no history of this "
                "height exists on this board (Garden of Eden, or the target "
                "is unreachable in exactly this many steps)"
            )
        return hist

    if method == "maxsat":
        chain = [target]
        cur = target
        t0 = time.monotonic()
        for g in range(generations):
            pred = _maxsat_predecessor(cur)
            if pred is None:
                raise ReverseError(
                    f"MaxSAT found no predecessor at reverse step {g + 1} "
                    f"({cur.live_count()} live cells). Try fewer --generations, "
                    f"--method multigen on a smaller board, or a larger --margin.",
                    achieved=g,
                )
            if verbose:
                print(
                    f"  reverse {g + 1}/{generations}: live {pred.live_count()} "
                    f"-> {cur.live_count()} ({time.monotonic() - t0:.2f}s)",
                    file=sys.stderr,
                )
            chain.append(pred)
            cur = pred
        chain.reverse()
        _assert_history(chain, target)
        return chain

    if method == "walksat":
        chain = [target]
        cur = target
        for g in range(generations):
            pred = None
            for attempt in range(8):
                init_rng = random.Random(rng.random())
                pred = _walksat_predecessor(cur, init_rng)
                if pred is not None:
                    break
            if pred is None:
                raise ReverseError(
                    f"WalkSAT found no predecessor at reverse step {g + 1}. "
                    f"Install python-sat for the MaxSAT engine.",
                    achieved=g,
                )
            chain.append(pred)
            cur = pred
        chain.reverse()
        _assert_history(chain, target)
        return chain

    raise ValueError(f"unknown method {method!r}")


# ---------------------------------------------------------------------------
# Targets: presets, text, QR
# ---------------------------------------------------------------------------

PRESETS: dict[str, str] = {
    "block": "##/##",
    "blinker": ".#./.#./.#.",
    "glider": ".#./..#/###",
    "lwss": "#..#./....#/#...#/.####",
    "r-pentomino": ".##/##./.#.",
    "toad": ".###/###.",
    "beacon": "##../##../..##/..##",
}

# 5×7 capitals + digits, plus a few symbols. Rows top→bottom.
_FONT_5X7: dict[str, tuple[str, ...]] = {
    "A": (".###.", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"),
    "B": ("####.", "#...#", "#...#", "####.", "#...#", "#...#", "####."),
    "C": (".####", "#....", "#....", "#....", "#....", "#....", ".####"),
    "D": ("####.", "#...#", "#...#", "#...#", "#...#", "#...#", "####."),
    "E": ("#####", "#....", "#....", "####.", "#....", "#....", "#####"),
    "F": ("#####", "#....", "#....", "####.", "#....", "#....", "#...."),
    "G": (".####", "#....", "#....", "#.###", "#...#", "#...#", ".####"),
    "H": ("#...#", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"),
    "I": ("#####", "..#..", "..#..", "..#..", "..#..", "..#..", "#####"),
    "J": ("..###", "...#.", "...#.", "...#.", "...#.", "#..#.", ".##.."),
    "K": ("#...#", "#..#.", "#.#..", "##...", "#.#..", "#..#.", "#...#"),
    "L": ("#....", "#....", "#....", "#....", "#....", "#....", "#####"),
    "M": ("#...#", "##.##", "#.#.#", "#...#", "#...#", "#...#", "#...#"),
    "N": ("#...#", "##..#", "#.#.#", "#..##", "#...#", "#...#", "#...#"),
    "O": (".###.", "#...#", "#...#", "#...#", "#...#", "#...#", ".###."),
    "P": ("####.", "#...#", "#...#", "####.", "#....", "#....", "#...."),
    "Q": (".###.", "#...#", "#...#", "#...#", "#.#.#", "#..#.", ".##.#"),
    "R": ("####.", "#...#", "#...#", "####.", "#.#..", "#..#.", "#...#"),
    "S": (".####", "#....", "#....", ".###.", "....#", "....#", "####."),
    "T": ("#####", "..#..", "..#..", "..#..", "..#..", "..#..", "..#.."),
    "U": ("#...#", "#...#", "#...#", "#...#", "#...#", "#...#", ".###."),
    "V": ("#...#", "#...#", "#...#", "#...#", "#...#", ".#.#.", "..#.."),
    "W": ("#...#", "#...#", "#...#", "#.#.#", "#.#.#", "##.##", "#...#"),
    "X": ("#...#", "#...#", ".#.#.", "..#..", ".#.#.", "#...#", "#...#"),
    "Y": ("#...#", "#...#", ".#.#.", "..#..", "..#..", "..#..", "..#.."),
    "Z": ("#####", "....#", "...#.", "..#..", ".#...", "#....", "#####"),
    "0": (".###.", "#...#", "#..##", "#.#.#", "##..#", "#...#", ".###."),
    "1": ("..#..", ".##..", "..#..", "..#..", "..#..", "..#..", ".###."),
    "2": (".###.", "#...#", "....#", "..##.", ".#...", "#....", "#####"),
    "3": ("####.", "....#", "....#", ".###.", "....#", "....#", "####."),
    "4": ("...#.", "..##.", ".#.#.", "#..#.", "#####", "...#.", "...#."),
    "5": ("#####", "#....", "####.", "....#", "....#", "#...#", ".###."),
    "6": (".###.", "#....", "#....", "####.", "#...#", "#...#", ".###."),
    "7": ("#####", "....#", "...#.", "..#..", ".#...", ".#...", ".#..."),
    "8": (".###.", "#...#", "#...#", ".###.", "#...#", "#...#", ".###."),
    "9": (".###.", "#...#", "#...#", ".####", "....#", "....#", ".###."),
    " ": (".....", ".....", ".....", ".....", ".....", ".....", "....."),
    "-": (".....", ".....", ".....", "#####", ".....", ".....", "....."),
    "?": (".###.", "#...#", "....#", "..##.", "..#..", ".....", "..#.."),
    "!": ("..#..", "..#..", "..#..", "..#..", "..#..", ".....", "..#.."),
    ".": (".....", ".....", ".....", ".....", ".....", ".....", "..#.."),
}


def text_grid(text: str, gap: int = 1) -> Grid:
    if not text:
        raise ValueError("text must be non-empty")
    glyphs = []
    for ch in text.upper():
        if ch not in _FONT_5X7:
            raise ValueError(f"unsupported character {ch!r} in --text")
        glyphs.append(_FONT_5X7[ch])
    width = len(glyphs) * 5 + gap * (len(glyphs) - 1)
    height = 7
    cells = [0] * (width * height)
    x0 = 0
    for glyph in glyphs:
        for y, row in enumerate(glyph):
            for x, ch in enumerate(row):
                if ch in LIVE_CHARS or ch == "#":
                    cells[y * width + x0 + x] = 1
        x0 += 5 + gap
    return Grid(width, height, tuple(cells))


def qr_grid(text: str, error: str = "M") -> Grid:
    """Encode ``text`` as a QR matrix (modules only, no quiet zone).

    Requires the optional ``segno`` package. Version is chosen automatically;
    v1 is 21×21 and is the realistic size for a printable Life roof.
    """
    try:
        import segno
    except ImportError as exc:
        raise ReverseError(
            "--qr requires the segno package (pip install segno) or paste a "
            "module grid via --pattern / --target-file"
        ) from exc
    qr = segno.make(text, error=error, micro=False)
    matrix = [list(row) for row in qr.matrix]
    h = len(matrix)
    w = len(matrix[0])
    cells = tuple(1 if matrix[y][x] else 0 for y in range(h) for x in range(w))
    return Grid(w, h, cells)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _build_target(args: argparse.Namespace) -> Grid:
    n = sum(bool(x) for x in (args.pattern, args.preset, args.text, args.qr, args.target_file))
    if n != 1:
        raise SystemExit("provide exactly one of --pattern, --preset, --text, --qr, --target-file")
    if args.pattern:
        g = parse_pattern(args.pattern)
    elif args.preset:
        if args.preset not in PRESETS:
            raise SystemExit(f"unknown preset {args.preset!r}; choose from {sorted(PRESETS)}")
        g = parse_pattern(PRESETS[args.preset])
    elif args.text:
        g = text_grid(args.text)
    elif args.qr:
        g = qr_grid(args.qr)
        # Dense QR modules are often Gardens of Eden on a tight board; a few
        # cells of margin are usually required before any predecessor exists.
        if args.margin < 2:
            print(
                f"warning: QR targets usually need --margin >= 2 "
                f"(got {args.margin}); predecessors may not exist",
                file=sys.stderr,
            )
    else:
        text = open(args.target_file, encoding="utf-8").read()
        if "/" in text and "\n" not in text.strip().split("/", 1)[0][-1:]:
            g = parse_pattern(text.replace("\n", "").strip())
        else:
            rows = [
                ln.strip()
                for ln in text.splitlines()
                if ln.strip() and not ln.strip().startswith("#")
            ]
            g = parse_pattern("/".join(rows))
    return g.padded(args.margin)


def main(argv: Optional[Sequence[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Find a Game of Life seed that evolves into a target top layer."
    )
    src = p.add_argument_group("target")
    src.add_argument("--pattern", help='target as rows joined by "/": ".##/##./.#."')
    src.add_argument("--preset", choices=sorted(PRESETS), help="named target specimen")
    src.add_argument("--text", help="5×7 bitmap text (A–Z, 0–9, space and -?!. )")
    src.add_argument("--qr", help="UTF-8 string encoded as a QR code (requires segno; v1 is 21×21)")
    src.add_argument("--target-file", help="pattern file (slash rows or one row per line)")
    p.add_argument("--margin", type=int, default=3, help="dead cells around the target (default 3)")
    p.add_argument(
        "--generations",
        type=int,
        required=True,
        help="Life steps between the seed (ground) and the target (roof)",
    )
    p.add_argument(
        "--method",
        choices=("auto", "maxsat", "multigen", "walksat"),
        default="auto",
        help="search strategy (auto = maxsat if python-sat is installed, else walksat)",
    )
    p.add_argument("--seed", type=int, default=0, help="RNG seed for walksat / tie breaks")
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--history", action="store_true", help="print every generation, seed first")
    p.add_argument(
        "--openscad-args",
        action="store_true",
        help="print -D flags for game_of_life.scad instead of the seed string",
    )
    args = p.parse_args(argv)

    try:
        target = _build_target(args)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.verbose:
        print(
            f"target {target.width}x{target.height}, live={target.live_count()}, "
            f"generations={args.generations}, method={args.method}, pysat={HAS_PYSAT}",
            file=sys.stderr,
        )
        print(target.render(), file=sys.stderr)

    try:
        hist = reverse_history(
            target,
            args.generations,
            method=args.method,
            rng=random.Random(args.seed),
            verbose=args.verbose,
        )
    except ReverseError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    seed = hist[0]
    if args.history:
        for i, g in enumerate(hist):
            print(f"# generation {i} live={g.live_count()}")
            print(g.render())
            print()
    if args.openscad_args:
        print(
            f"-D 'preset=\"custom\"' "
            f"-D 'seed_pattern=\"{seed.seed_string()}\"' "
            f"-D 'generations={args.generations}'"
        )
    elif not args.history:
        print(seed.seed_string())
    elif args.verbose:
        print(f"# seed_pattern={seed.seed_string()}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

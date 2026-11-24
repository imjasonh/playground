"""The addresses that the image files name, for the generators.

A generator writes an address as `(img% name)` and reads the name's value
here, so that its output follows the image after a rebuild.
"""

import os
import re

TREE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "C3BootProofs")
IMAGE = os.path.join(TREE, "Image")
MODULES = ["Bootloader", "BootloaderData"] + [f"BootloaderData{i}" for i in range(2, 8)]


def _load():
    names, data, module = {}, [], {}
    for mod in MODULES:
        text = open(os.path.join(IMAGE, mod + ".lean")).read()
        lists = {m.group(1): len(re.findall(r"0x[0-9a-f]+", m.group(2)))
                 for m in re.finditer(r"^def (\w+) : List Nat :=\s*\[([^\]]*)\]", text, re.M)}
        for m in re.finditer(r"^def (\w+) : Nat := (0x[0-9a-f]+)$", text, re.M):
            names[m.group(1)] = int(m.group(2), 16)
            module[m.group(1)] = "C3BootProofs.Image." + mod
            item = m.group(1)[:-len("Address")]
            if m.group(1).endswith("Address") and item + "Code" not in lists:
                data.append((item, int(m.group(2), 16), lists.get(item + "Data", 0)))
    return names, [d for d in data if d[0] + "Size" not in names], module


NAMES, DATA, MODULE = _load()


def address(name):
    """The value of `{name}Address`."""
    return NAMES[name + "Address"]


def data_expr(a):
    """`(img% item + off)` for an address in a data item, or None."""
    cands = [(a != s, a - s, k, n) for k, (n, s, size) in enumerate(DATA) if s <= a < s + size or a == s]
    if not cands:
        return None
    _, off, _, n = min(cands)
    return f"(img% {n}Address)" if off == 0 else f"(img% {n}Address + 0x{off:X})"


def hi20(a):
    return (a + 0x800) // 0x1000 * 0x1000 % 2**32


def lo12(a):
    return a % 0x1000 if a % 0x1000 < 0x800 else a % 0x1000 + 0xFFFFF000


def _imports(mod):
    path = os.path.join(TREE, *mod.split(".")[1:]) + ".lean"
    return re.findall(r"^import (\S+)", open(path).read(), re.M) if os.path.exists(path) else []


def add_imports(text):
    """`text` with an import for each image module its `img%` names need."""
    seen, todo = set(), re.findall(r"^import (\S+)", text, re.M)
    while todo:
        mod = todo.pop()
        if mod not in seen:
            seen.add(mod)
            todo += _imports(mod)
    used = {MODULE[n] for e in re.findall(r"img% ([^)]*)", text) for n in re.findall(r"\w+", e) if n in MODULE}
    for mod in sorted(used - seen):
        last = list(re.finditer(r"^import \S+\n", text, re.M))[-1].end()
        text = text[:last] + f"import {mod}\n" + text[last:]
    return text

#!/usr/bin/env python3
"""Extract symbols from KiCad .kicad_sym libraries into embedded lib_symbols form.

Parent symbols keep the ``Library:Name`` id; nested unit symbols drop the
library prefix (``Name_0_1``, not ``Library:Name_0_1``). That is what KiCad
expects inside a schematic's ``lib_symbols`` block.
"""

from __future__ import annotations

import re
from pathlib import Path


def _balanced_block(text: str, start: int) -> str:
    depth = 0
    for i, ch in enumerate(text[start:], start):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError("unbalanced s-expression")


def extract_symbol(library_path: str | Path, symbol_name: str) -> str:
    """Return the raw ``(symbol "Name" ...)`` block from a .kicad_sym file."""
    text = Path(library_path).read_text()
    needle = f'(symbol "{symbol_name}"'
    start = text.find(needle)
    if start < 0:
        raise KeyError(f"{symbol_name} not in {library_path}")
    return _balanced_block(text, start)


def to_embedded(lib_name: str, symbol_block: str) -> str:
    """Rewrite a library symbol block for embedding under ``lib_symbols``.

    - Parent becomes ``Library:Name``.
    - Nested ``Name_x_y`` units stay unprefixed.
    - Indent one level for nesting under ``(lib_symbols ...)``.
    """
    m = re.match(r'\(symbol "([^"]+)"', symbol_block)
    if not m:
        raise ValueError("not a symbol block")
    short = m.group(1)
    full = f"{lib_name}:{short}"

    # Only rewrite the outermost symbol name.
    out = symbol_block.replace(f'(symbol "{short}"', f'(symbol "{full}"', 1)

    # Nested units in KiCad libs are already unprefixed (Name_0_1). Leave them.
    # Indent every line by 4 spaces for lib_symbols nesting.
    indented = "\n".join("    " + line if line.strip() else line for line in out.splitlines())
    return indented


def embed(library_path: str | Path, lib_name: str, symbol_name: str) -> str:
    """Extract and convert one symbol for schematic embedding."""
    return to_embedded(lib_name, extract_symbol(library_path, symbol_name))


if __name__ == "__main__":
    import sys

    print(embed(sys.argv[1], sys.argv[2], sys.argv[3])[:500])

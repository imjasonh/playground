#!/usr/bin/env python3
"""Tiny pty fixture. Prints a two-cell screen and exits on x."""

import os


def show(text: str) -> None:
    os.write(1, b"\x1b[H\x1b[2J" + text.encode("ascii") + b"\n")


def main() -> int:
    show("@.")
    while True:
        key = os.read(0, 1)
        if key in (b"", b"x"):
            show("BYE")
            return 0
        if key == b"l":
            show(".@")
        else:
            show("@.")


if __name__ == "__main__":
    raise SystemExit(main())

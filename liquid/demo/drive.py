#!/usr/bin/env python3
"""Record a demo of liquid by driving it with scripted mouse and keyboard input.

The script runs `asciinema rec` in a pseudo-terminal and writes the same
bytes a terminal sends when you move the mouse, click, and type: SGR mouse
reports such as ESC [ < 0 ; 40 ; 12 M. The program can't tell the difference,
so the recording shows real input going through Bubble Tea and bubblezone.

Usage: drive.py LIQUID_BINARY OUTPUT.cast
"""

import fcntl
import json
import math
import os
import pty
import select
import struct
import sys
import termios
import time

# GitHub serves images in pull requests and READMEs through a proxy that
# rejects files over 5 MiB. At this size, 15 frames per second, and about 35
# seconds, the GIF stays under that.
COLS, ROWS = 100, 30
# The tank starts below the one-line header, inside a one-cell border.
TANK_X, TANK_Y = 1, 2
TANK_W, TANK_H = COLS - 2, ROWS - 4

LEFT, MIDDLE, RIGHT, NO_BUTTON = 0, 1, 2, 3
SHIFT, ALT, CTRL = 4, 8, 16
MOTION = 32


def report(code, col, row, release=False):
    """Return an SGR mouse report for a screen cell. Reports count from 1."""
    return f"\x1b[<{code};{col + 1};{row + 1}{'m' if release else 'M'}".encode()


def mouse(code, x, y, release=False):
    """Return an SGR mouse report for tank cell (x, y)."""
    x = min(max(round(x), 0), TANK_W - 1) + TANK_X
    y = min(max(round(y), 0), TANK_H - 1) + TANK_Y
    return report(code, x, y, release)


def line(x0, y0, x1, y1, n):
    return [(x0 + (x1 - x0) * i / n, y0 + (y1 - y0) * i / n) for i in range(n + 1)]


def arc(cx, cy, r, start, end, n):
    """Return points on a circle that looks round: cells are twice as tall as wide."""
    pts = []
    for i in range(n + 1):
        a = math.radians(start + (end - start) * i / n)
        pts.append((cx + 2 * r * math.cos(a), cy + r * math.sin(a)))
    return pts


class Terminal:
    def __init__(self, fd):
        self.fd = fd

    def wait(self, seconds):
        """Drain the program's output for the given time."""
        end = time.monotonic() + seconds
        while (left := end - time.monotonic()) > 0:
            ready, _, _ = select.select([self.fd], [], [], left)
            if ready:
                try:
                    if not os.read(self.fd, 1 << 16):
                        return
                except OSError:
                    return

    def send(self, data, pause=0.0):
        os.write(self.fd, data)
        self.wait(pause)

    def key(self, k, pause=0.6):
        self.send(k.encode() if isinstance(k, str) else k, pause)

    def hover(self, path, dt=0.03, mod=0):
        for x, y in path:
            self.send(mouse(NO_BUTTON + MOTION + mod, x, y), dt)

    def leave(self):
        """Move the cursor off the tank, onto the header."""
        self.send(report(NO_BUTTON + MOTION, COLS // 2, 0), 0.1)

    def wheel(self, x, y, up=True, times=1):
        for _ in range(times):
            self.send(mouse(64 if up else 65, x, y), 0.08)

    def drag(self, button, path, dt=0.03, mod=0):
        x, y = path[0]
        self.send(mouse(button + mod, x, y), dt)
        for x, y in path[1:]:
            self.send(mouse(button + MOTION + mod, x, y), dt)
        self.send(mouse(button + mod, x, y, release=True), 0)


UP, DOWN, RIGHT_ARROW, LEFT_ARROW = "\x1b[A", "\x1b[B", "\x1b[C", "\x1b[D"


def perform(t):
    W, H = TANK_W, TANK_H
    # The dam breaks and crashes into the far wall.
    t.wait(2.3)

    # Hover in from the right, then drag through the liquid to push it away.
    t.hover(line(W * 0.95, H * 0.3, W * 0.75, H * 0.55, 8), dt=0.03)
    t.drag(LEFT, line(W * 0.75, H * 0.62, W * 0.2, H * 0.72, 40), dt=0.035)
    t.wait(0.3)
    t.drag(LEFT, [(W * 0.5, H * 0.88)] * 15, dt=0.03)
    t.wait(0.7)

    # Grow the brush, pull a blob out of the pool, carry it around, and drop it.
    t.hover(line(W * 0.5, H * 0.6, W * 0.35, H * 0.7, 6), dt=0.03)
    t.wheel(W * 0.35, H * 0.7, times=2)
    t.drag(RIGHT, line(W * 0.35, H * 0.85, W * 0.38, H * 0.55, 12)
           + arc(W * 0.5, H * 0.42, H * 0.2, 180, 480, 52), dt=0.04)
    t.wait(1.2)

    # Hold Shift while skimming the surface to attract, then Ctrl to disperse.
    t.wheel(W * 0.15, H * 0.55, up=False, times=2)
    t.hover(line(W * 0.12, H * 0.64, W * 0.8, H * 0.6, 52), dt=0.035, mod=SHIFT)
    t.hover(line(W * 0.55, H * 0.8, W * 0.25, H * 0.82, 32), dt=0.035, mod=CTRL)
    t.leave()

    # Tilt the tank.
    t.key(LEFT_ARROW, 1.3)
    t.key(RIGHT_ARROW, 1.3)
    t.key(DOWN, 0.9)

    # Two liquids that mix.
    for _ in range(3):
        t.key("c", 0.1)
    t.key("2", 2.3)
    t.drag(LEFT, line(W * 0.5, H * 0.3, W * 0.5, H * 0.95, 16)
           + arc(W * 0.5, H * 0.75, H * 0.12, 270, 990, 64), dt=0.03)
    t.wait(1.0)

    # The other views.
    t.key("v", 1.2)
    t.drag(LEFT, line(W * 0.2, H * 0.8, W * 0.8, H * 0.8, 26), dt=0.03)
    t.wait(0.3)
    t.key("v", 1.5)
    t.key("v", 0.3)

    # A zero-gravity blob of lava, pulled around and burst.
    for _ in range(3):
        t.key("c", 0.1)
    t.key("5", 1.0)
    t.drag(RIGHT, line(W * 0.5, H * 0.5, W * 0.7, H * 0.4, 16)
           + arc(W * 0.5, H * 0.45, H * 0.22, 0, 300, 44), dt=0.035)
    t.wait(0.4)
    t.drag(LEFT, [(W * 0.45, H * 0.45)] * 10, dt=0.03)
    t.wait(1.8)

    # Every control.
    t.leave()
    t.key("?", 2.2)
    t.key("q", 0.5)


def trim_exit(path):
    """Cut the recording where the program leaves the alternate screen.

    Otherwise the recording, and the GIF made from it, ends on the empty
    screen the program returns to when it quits.
    """
    with open(path) as f:
        lines = f.read().splitlines()
    for i, line in enumerate(lines[1:], start=1):
        event = json.loads(line)
        if event[1] == "o" and "\x1b[?1049l" in event[2]:
            lines = lines[:i]
            break
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    binary, out = sys.argv[1], sys.argv[2]
    pid, fd = pty.fork()
    if pid == 0:
        fcntl.ioctl(0, termios.TIOCSWINSZ, struct.pack("HHHH", ROWS, COLS, 0, 0))
        os.environ.update(TERM="xterm-256color", COLORTERM="truecolor")
        os.environ.pop("NO_COLOR", None)
        cmd = f"{binary} -seed 7"
        os.execvp("asciinema", ["asciinema", "rec", "--quiet", "--overwrite",
                                "--window-size", f"{COLS}x{ROWS}", "-c", cmd, out])
    t = Terminal(fd)
    t.wait(1.0)
    perform(t)
    t.wait(1.0)
    os.waitpid(pid, 0)
    trim_exit(out)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Capture ESP32 Mask-ROM gzip-bench serial output, symbolize 2 kHz PC profiles,
and emit an SVG flame chart.

Usage:
  python3 scripts/gzip-bench-profile.py --port /dev/cu.usbmodem5ABA0252061 \
      --elf target/waveshare-epd75-nobt/xtensa-esp32-espidf/release/waveshare-epd75-gzip-bench \
      --svg docs/esp32-rom-miniz-flamegraph.svg

  # Or re-symbolize a previously captured serial log:
  python3 scripts/gzip-bench-profile.py --log /tmp/gzip-bench.log --elf ... --svg ...
"""

from __future__ import annotations

import argparse
import fcntl
import glob
import html
import os
import re
import select
import struct
import subprocess
import sys
import termios
import time

PHASE_ORDER = [
    "rom_tinfl_240m",
    "rom_tdefl_p1_greedy",
    "rom_tdefl_p16_fast",
    "rom_tdefl_p128_default",
    "rom_tdefl_p4095_max",
    "rom_tdefl_p0_huff",
    "rom_crc32_240m",
]

PHASE_LABELS = {
    "rom_tinfl_240m": "1. Mask-ROM tinfl_decompress @ 240 MHz",
    "rom_tdefl_p1_greedy": "2. Mask-ROM tdefl_compress (probes=1 greedy) @ 240 MHz",
    "rom_tdefl_p16_fast": "3. Mask-ROM tdefl_compress (probes=16 lazy) @ 240 MHz",
    "rom_tdefl_p128_default": "4. Mask-ROM tdefl_compress (probes=128 default) @ 240 MHz",
    "rom_tdefl_p4095_max": "5. Mask-ROM tdefl_compress (probes=4095 max) @ 240 MHz",
    "rom_tdefl_p0_huff": "6. Mask-ROM tdefl_compress (probes=0 Huffman-only) @ 240 MHz",
    "rom_crc32_240m": "7. Mask-ROM mz_crc32 @ 240 MHz",
}


def capture_serial(port: str, timeout_s: float, save_log: str | None) -> str:
    """Reset the ESP32 over RTS and read 115200 baud output until BENCH_DONE."""
    fd = os.open(port, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
    try:
        attrs = termios.tcgetattr(fd)
        attrs[0] = 0
        attrs[1] = 0
        attrs[2] = termios.CS8 | termios.CREAD | termios.CLOCAL
        attrs[3] = 0
        attrs[4] = termios.B115200
        attrs[5] = termios.B115200
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
        termios.tcflush(fd, termios.TCIOFLUSH)

        # Pulse RTS (EN low -> high, IO0 high) to reset the ESP32 into normal boot.
        tiocmget = 0x4004746A if sys.platform == "darwin" else 0x5415
        tiocmset = 0x8004746D if sys.platform == "darwin" else 0x5418
        tiocm_dtr = 0x002
        tiocm_rts = 0x004

        def set_lines(dtr: bool, rts: bool) -> None:
            bits = struct.unpack("I", fcntl.ioctl(fd, tiocmget, struct.pack("I", 0)))[0]
            bits = (bits | tiocm_dtr) if dtr else (bits & ~tiocm_dtr)
            bits = (bits | tiocm_rts) if rts else (bits & ~tiocm_rts)
            fcntl.ioctl(fd, tiocmset, struct.pack("I", bits))

        set_lines(False, True)
        time.sleep(0.1)
        termios.tcflush(fd, termios.TCIOFLUSH)
        set_lines(False, False)

        buf = bytearray()
        started = False
        deadline = time.time() + timeout_s
        while time.time() < deadline:
            readable, _, _ = select.select([fd], [], [], 0.5)
            if not readable:
                continue
            chunk = os.read(fd, 4096)
            if not chunk:
                continue
            buf.extend(chunk)
            if b"BENCH_START" in buf:
                started = True
            if started and b"BENCH_DONE" in buf:
                break
    finally:
        os.close(fd)

    text = buf.decode("utf-8", "replace")
    if save_log:
        os.makedirs(os.path.dirname(os.path.abspath(save_log)), exist_ok=True)
        with open(save_log, "w", encoding="utf-8") as fh:
            fh.write(text)
    return text


def find_tool(patterns: list[str]) -> str | None:
    for pat in patterns:
        matches = sorted(glob.glob(pat, recursive=True))
        if matches:
            return matches[-1]
    return None


def resolve_pcs(addr2line: str | None, elf: str | None, pcs: list[int]) -> dict[int, tuple[str, str]]:
    if not pcs or not addr2line or not elf or not os.path.exists(elf):
        return {pc: (f"{pc:#010x}", "?") for pc in pcs}
    cmd = [addr2line, "-f", "-C", "-e", elf] + [f"{pc:#x}" for pc in pcs]
    out = subprocess.check_output(cmd, text=True, errors="replace").splitlines()
    result: dict[int, tuple[str, str]] = {}
    for idx, pc in enumerate(pcs):
        fn = out[2 * idx].strip() if 2 * idx < len(out) else f"{pc:#010x}"
        loc = out[2 * idx + 1].strip().rsplit("/", 1)[-1] if 2 * idx + 1 < len(out) else "?"
        result[pc] = (fn, loc)
    return result


def write_flamegraph_svg(
    svg_path: str,
    cpu_mhz: float,
    svg_phases: list[tuple[str, int, list[tuple[str, int]]]],
) -> None:
    width = 1140
    row_h = 26
    phase_gap = 42
    pad_x = 24
    bar_w = width - 2 * pad_x
    height = 74 + len(svg_phases) * (row_h * 2 + phase_gap) + 16
    palette = ["#d9534f", "#f0ad4e", "#5cb85c", "#428bca", "#8e6cc0", "#3aa6a6", "#d96b98"]

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        "<style>",
        '  text { font-family: -apple-system, BlinkMacSystemFont, "SF Mono", Menlo, monospace; }',
        "  .title { font-size: 17px; font-weight: 700; fill: #1a1f2c; }",
        "  .sub { font-size: 12px; fill: #556070; }",
        "  .ptitle { font-size: 12.5px; font-weight: 700; fill: #1a1f2c; }",
        "  .lbl { font-size: 10.5px; fill: #ffffff; font-weight: 600; }",
        "</style>",
        f'<rect width="{width}" height="{height}" fill="#fafbfc" rx="8"/>',
        f'<text x="{pad_x}" y="30" class="title">ESP32 Silicon Mask-ROM miniz ({cpu_mhz:.0f} MHz Xtensa LX6) — 2 kHz PC Flame Chart</text>',
        f'<text x="{pad_x}" y="49" class="sub">Symbolized directly against esp32_rev300_rom.elf — authentic Mask-ROM tinfl, tdefl, and mz_crc32</text>',
    ]
    y = 74
    for phase, total_all, buckets in svg_phases:
        title = PHASE_LABELS.get(phase, phase)
        lines.append(
            f'<text x="{pad_x}" y="{y}" class="ptitle">{html.escape(title)}  [n={total_all} samples]</text>'
        )
        y += 7
        lines.append(
            f'<rect x="{pad_x}" y="{y}" width="{bar_w}" height="{row_h - 4}" fill="#2d3748" rx="3"/>'
        )
        lines.append(
            f'<text x="{pad_x + 8}" y="{y + 15}" class="lbl">{html.escape(phase)} (100%)</text>'
        )
        y += row_h
        x = float(pad_x)
        for idx, (fn, hits) in enumerate(buckets):
            frac = hits / max(total_all, 1)
            w = frac * bar_w
            if w < 1.5:
                continue
            color = "#9aa5b1" if "other" in fn else palette[idx % len(palette)]
            pct = 100.0 * frac
            lines.append(
                f'<rect x="{x:.1f}" y="{y}" width="{max(w - 1, 1):.1f}" height="{row_h - 2}" fill="{color}" rx="2">'
                f"<title>{html.escape(fn)}: {hits} ({pct:.1f}%)</title></rect>"
            )
            if w > 55:
                max_chars = int((w - 10) / 6.4)
                txt = f"{fn} ({pct:.0f}%)"
                if len(txt) > max_chars:
                    txt = txt[: max(max_chars - 1, 1)] + "…"
                lines.append(
                    f'<text x="{x + 5:.1f}" y="{y + 16}" class="lbl">{html.escape(txt)}</text>'
                )
            x += w
        y += row_h + phase_gap - 7
    lines.append("</svg>")

    os.makedirs(os.path.dirname(os.path.abspath(svg_path)), exist_ok=True)
    with open(svg_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description="Capture & symbolize ESP32 Mask-ROM gzip-bench output")
    parser.add_argument("--port", default="/dev/cu.usbmodem5ABA0252061", help="Serial port path")
    parser.add_argument("--log", help="Parse an existing serial log instead of reading --port")
    parser.add_argument("--save-log", help="Optional path to save raw serial capture")
    parser.add_argument("--elf", help="Path to waveshare-epd75-gzip-bench ELF")
    parser.add_argument("--rom-elf", help="Path to esp32_rev300_rom.elf (auto-detected under .embuild)")
    parser.add_argument("--svg", default="docs/esp32-rom-miniz-flamegraph.svg", help="Output SVG flame chart path")
    parser.add_argument("--timeout", type=float, default=120.0, help="Serial capture timeout in seconds")
    args = parser.parse_args()

    if args.log:
        with open(args.log, encoding="utf-8", errors="replace") as fh:
            raw_text = fh.read()
    else:
        raw_text = capture_serial(args.port, args.timeout, args.save_log)

    parts = raw_text.split("BENCH_START ")
    first_run = ("BENCH_START " + parts[1]) if len(parts) > 1 else raw_text

    cpu_mhz = 240.0
    benches = []
    phases: dict[str, list[tuple[int, int]]] = {}
    totals: dict[str, int] = {}

    for line in first_run.splitlines():
        s = line.strip()
        m = re.search(r"BENCH_START .*cpu_hz=(\d+)", s)
        if m:
            cpu_mhz = int(m.group(1)) / 1_000_000.0
            print(s)
        elif s.startswith("TDEFL_ALLOC "):
            print(s)
        m = re.match(
            r"BENCH kind=(\S+) impl=(\S+) corpus=(\S+) iters=(\d+) in_bytes=(\d+) out_bytes=(\d+) total_us=(\d+)",
            s,
        )
        if m:
            benches.append(m.groups())
        m = re.match(r"PROF_SUMMARY phase=(\S+) total_samples=(\d+) unique_pcs=(\d+)", s)
        if m:
            totals[m.group(1)] = int(m.group(2))
        m = re.match(r"PROF phase=(\S+) pc=(0x[0-9a-fA-F]+) hits=(\d+)", s)
        if m:
            phases.setdefault(m.group(1), []).append((int(m.group(2), 16), int(m.group(3))))

    print(f"\n=== Benchmark Throughput @ {cpu_mhz:.0f} MHz ===")
    for kind, impl, corpus, iters_s, in_s, out_s, us_s in benches:
        iters, in_b, out_b, us = int(iters_s), int(in_s), int(out_s), int(us_s)
        bpi = out_b if kind == "inflate" else in_b
        tot_b = bpi * iters
        mbps = tot_b / max(us, 1)
        cyc_b = (us * cpu_mhz) / max(tot_b, 1)
        ratio = (out_b / max(in_b, 1)) if kind == "inflate" else (in_b / max(out_b, 1))
        print(
            f"  {kind:11s} {impl:22s} {corpus:14s} | {us / iters:7.1f} us/op | "
            f"{mbps:6.2f} MB/s | {cyc_b:5.1f} cyc/B | {in_b}->{out_b} ({ratio:.2f}x)"
        )

    addr2line = find_tool([".embuild/**/xtensa-esp32-elf-addr2line"])
    rom_elf = args.rom_elf or find_tool(
        [".embuild/tools/esp-rom-elfs/**/esp32*rev300*rom.elf", ".embuild/tools/esp-rom-elfs/**/esp32*rom.elf"]
    )

    svg_phases: list[tuple[str, int, list[tuple[str, int]]]] = []
    for phase in PHASE_ORDER:
        items = phases.get(phase, [])
        if not items:
            continue
        top_sum = sum(h for _, h in items)
        total_all = totals.get(phase, top_sum)
        rom_pcs = [pc for pc, _ in items if pc < 0x40070000]
        app_pcs = [pc for pc, _ in items if pc >= 0x40070000]
        rom_map = resolve_pcs(addr2line, rom_elf, rom_pcs)
        app_map = resolve_pcs(addr2line, args.elf, app_pcs)
        by_fn: dict[str, int] = {}
        for pc, hits in items:
            if pc < 0x40070000:
                fn = f"ROM:{rom_map[pc][0]}"
            else:
                fn = app_map[pc][0]
            by_fn[fn] = by_fn.get(fn, 0) + hits
        if total_all > top_sum:
            by_fn["(other ROM tail PCs)"] = total_all - top_sum
        svg_phases.append((phase, total_all, sorted(by_fn.items(), key=lambda x: -x[1])))

    if svg_phases and args.svg:
        write_flamegraph_svg(args.svg, cpu_mhz, svg_phases)
        print(f"\nWrote SVG flame chart: {args.svg}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

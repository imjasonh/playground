#!/usr/bin/env python3
"""Capture the store screenshots from a real Chrome window.

This starts Xvfb at 1280 by 800, serves a page, and loads this directory
with Chrome for Testing. store/screenshot.png is that window with two tabs
at the same URL and the toolbar badge. store/screenshot-closed.png is the
same window after the toolbar click.

Branded Chrome ignores --load-extension. Set CHROME_BIN to a Chrome for
Testing binary. The script also needs Xvfb, ImageMagick's import, and xdotool.
"""

from __future__ import annotations

import hashlib
import json
import os
import signal
import subprocess
import time
from pathlib import Path

from PIL import Image

HERE = Path(__file__).resolve().parent
PAGE = "<!DOCTYPE html><html><head><meta charset=\"utf-8\"><title>Notes</title></head><body><p>Notes</p></body></html>\n"


def extension_id(path: Path) -> str:
    digest = hashlib.sha256(str(path).encode()).hexdigest()
    return "".join(chr(ord("a") + int(char, 16)) for char in digest[:32])


def find_chrome() -> str:
    chosen = os.environ.get("CHROME_BIN", "")
    if chosen:
        return chosen
    roots = [Path("/tmp/chrome-for-testing"), Path.home() / "chrome"]
    for root in roots:
        if not root.is_dir():
            continue
        for path in sorted(root.glob("**/chrome")):
            if path.is_file() and os.access(path, os.X_OK):
                return str(path)
    raise SystemExit("Set CHROME_BIN to a Chrome for Testing binary. Branded Chrome ignores --load-extension.")


def start(args: list[str], env: dict[str, str] | None = None) -> subprocess.Popen:
    return subprocess.Popen(
        args,
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def stop(proc: subprocess.Popen | None) -> None:
    if proc is None or proc.poll() is not None:
        return
    os.killpg(proc.pid, signal.SIGTERM)
    deadline = time.time() + 5
    while time.time() < deadline and proc.poll() is None:
        time.sleep(0.1)
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait(timeout=5)


def chrome_args(chrome: str, profile: Path, urls: list[str]) -> list[str]:
    return [
        chrome,
        "--no-sandbox",
        "--disable-gpu",
        "--disable-dev-shm-usage",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-sync",
        "--disable-background-networking",
        "--disable-component-update",
        "--window-position=0,0",
        "--window-size=1280,800",
        f"--user-data-dir={profile}",
        f"--load-extension={HERE}",
        f"--disable-extensions-except={HERE}",
        *urls,
    ]


def wait_for_window(display: str) -> None:
    deadline = time.time() + 15
    while time.time() < deadline:
        result = subprocess.run(
            ["xwininfo", "-root", "-tree"],
            env={**os.environ, "DISPLAY": display},
            check=False,
            capture_output=True,
            text=True,
        )
        if "Google Chrome for Testing" in result.stdout or "Google Chrome" in result.stdout:
            return
        time.sleep(0.2)
    raise SystemExit("Chrome did not open a window")


def blue_clusters(image: Image.Image) -> list[tuple[int, int, int, int]]:
    image = image.convert("RGB")
    points: list[tuple[int, int]] = []
    for y in range(45, 85):
        for x in range(1000, 1240):
            red, green, blue = image.getpixel((x, y))[:3]
            if blue > 150 and red < 90 and 40 < green < 130:
                points.append((x, y))
    points.sort()
    groups: list[list[tuple[int, int]]] = []
    for point in points:
        if not groups or point[0] - groups[-1][-1][0] > 15:
            groups.append([point])
        else:
            groups[-1].append(point)
    boxes = []
    for group in groups:
        xs = [point[0] for point in group]
        ys = [point[1] for point in group]
        boxes.append((min(xs), min(ys), max(xs), max(ys)))
    return boxes


def wait_for_badge(display: str) -> tuple[int, int]:
    deadline = time.time() + 10
    while time.time() < deadline:
        path = Path("/tmp/duplicate-tabs-probe.png")
        grab(display, path)
        image = Image.open(path)
        clusters = [box for box in blue_clusters(image) if box[2] - box[0] < 30]
        if clusters:
            left, top, right, bottom = clusters[0]
            return (left + right) // 2, (top + bottom) // 2
        time.sleep(0.3)
    raise SystemExit("the toolbar badge did not appear")


def grab(display: str, path: Path) -> None:
    subprocess.run(
        ["import", "-window", "root", "-depth", "8", f"png24:{path}"],
        env={**os.environ, "DISPLAY": display},
        check=True,
    )


def save_rgb(display: str, path: Path) -> None:
    raw = path.with_suffix(".raw.png")
    grab(display, raw)
    image = Image.open(raw).convert("RGB")
    if image.size != (1280, 800):
        raise SystemExit(f"{path.name} is {image.size}, want 1280x800")
    image.save(path, "PNG")
    raw.unlink()


def move(display: str, x: int, y: int, click: bool = False) -> None:
    args = ["xdotool", "mousemove", str(x), str(y)]
    if click:
        args.append("click")
        args.append("1")
    subprocess.run(args, env={**os.environ, "DISPLAY": display}, check=True)


def pin_extension(profile: Path, extension: str) -> None:
    prefs_path = profile / "Default" / "Preferences"
    prefs = json.loads(prefs_path.read_text())
    extensions = prefs.setdefault("extensions", {})
    extensions["pinned_extensions"] = [extension]
    prefs_path.write_text(json.dumps(prefs))


def launch_chrome(chrome: str, profile: Path, display: str, urls: list[str]) -> subprocess.Popen:
    env = {**os.environ, "DISPLAY": display}
    proc = subprocess.Popen(
        chrome_args(chrome, profile, urls),
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    return proc


def main() -> None:
    chrome = find_chrome()
    extension = extension_id(HERE)
    store = HERE / "store"
    store.mkdir(exist_ok=True)
    page_dir = Path("/tmp/duplicate-tabs-page")
    page_dir.mkdir(exist_ok=True)
    (page_dir / "index.html").write_text(PAGE)
    profile = Path("/tmp/duplicate-tabs-chrome-profile")
    if profile.exists():
        subprocess.run(["rm", "-rf", str(profile)], check=True)
    profile.mkdir()
    display = ":89"
    url = "http://127.0.0.1:8765/"
    xvfb = None
    server = None
    browser = None
    try:
        xvfb = start(["Xvfb", display, "-screen", "0", "1280x800x24", "-ac"])
        time.sleep(0.4)
        server = start(["python3", "-m", "http.server", "8765", "--bind", "127.0.0.1", "--directory", str(page_dir)])
        browser = launch_chrome(chrome, profile, display, [url])
        wait_for_window(display)
        time.sleep(2)
        stop(browser)
        browser = None
        pin_extension(profile, extension)
        browser = launch_chrome(chrome, profile, display, [url, url])
        wait_for_window(display)
        badge_x, badge_y = wait_for_badge(display)
        move(display, 400, 500)
        time.sleep(0.4)
        save_rgb(display, store / "screenshot.png")
        move(display, badge_x, badge_y, click=True)
        time.sleep(0.8)
        move(display, 400, 500)
        time.sleep(0.6)
        save_rgb(display, store / "screenshot-closed.png")
    finally:
        stop(browser)
        stop(server)
        stop(xvfb)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Render the moving-sign clip that LiveTranslateClipTests reads.

The clip is five seconds of a Spanish door sign filmed by an unsteady hand. The
camera holds, pans, shakes hard enough to blur, zooms in, and drifts back. OCR
readings also churn the way they do on a real camera: fine print that is read
only some of the time, a room plate cut off by the frame edge, and a glare that
washes out part of the sign. The camera path and noise are fixed, so a rerun
with the same Pillow and ffmpeg produces the same frames. Next to the clip, it
writes a JSON file with where each sign line sits in every frame, which tests
use as ground truth.

Requires Pillow, NumPy, and ffmpeg. From the repo root:

    python3 ios/scripts/make-live-translate-clip.py

To also keep the PNG frames, pass --frames DIR.
"""

import argparse
import json
import math
import pathlib
import shutil
import subprocess
import tempfile

import numpy as np
from PIL import Image, ImageDraw, ImageFilter, ImageFont

WIDTH, HEIGHT = 720, 1280
FPS = 24
SECONDS = 5
SCENE_W, SCENE_H = 2200, 3400
SIGN_W, SIGN_H = 1060, 820
FONT_DIR = pathlib.Path("/usr/share/fonts/truetype/dejavu")

# (text, font size in scene pixels, bold, color)
LINES = [
    ("SALIDA DE EMERGENCIA", 70, True, (176, 24, 28)),
    ("Mantenga la puerta cerrada", 62, False, (24, 24, 28)),
    ("Prohibido fumar", 62, True, (24, 24, 28)),
    ("Solo personal autorizado", 62, False, (24, 24, 28)),
]
FINE_PRINT = "Ley 31/1995 de Prevención de Riesgos Laborales"

DEFAULT_OUT = (
    pathlib.Path(__file__).resolve().parent.parent
    / "Tests/PlaygroundTests/Fixtures/LiveTranslate/moving-sign.mp4"
)


def font(size, bold):
    name = "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf"
    return ImageFont.truetype(str(FONT_DIR / name), size)


def scene():
    """Wall with a sign on it, in scene pixels, and the box of each line in LINES."""
    wall = np.zeros((SCENE_H, SCENE_W, 3), dtype=np.float32)
    rows = np.linspace(0, 1, SCENE_H, dtype=np.float32)[:, None]
    wall[..., 0] = 206 - 18 * rows
    wall[..., 1] = 198 - 16 * rows
    wall[..., 2] = 184 - 14 * rows
    grain = np.random.default_rng(7).normal(0, 3, (SCENE_H, SCENE_W, 1)).astype(np.float32)
    wall += grain
    image = Image.fromarray(np.clip(wall, 0, 255).astype(np.uint8))

    left = (SCENE_W - SIGN_W) // 2
    top = (SCENE_H - SIGN_H) // 2
    shadow = Image.new("L", image.size, 0)
    ImageDraw.Draw(shadow).rounded_rectangle(
        (left + 14, top + 18, left + SIGN_W + 14, top + SIGN_H + 18), radius=36, fill=110
    )
    shadow = shadow.filter(ImageFilter.GaussianBlur(18))
    image.paste((60, 52, 44), mask=shadow)

    draw = ImageDraw.Draw(image)
    draw.rounded_rectangle(
        (left, top, left + SIGN_W, top + SIGN_H),
        radius=36,
        fill=(250, 249, 244),
        outline=(70, 70, 74),
        width=6,
    )
    y = top + 90
    line_boxes = []
    for text, size, bold, color in LINES:
        line_boxes.append(centered(draw, text, font(size, bold), left + SIGN_W / 2, y, color))
        y += int(size * 2.35)
    centered(draw, FINE_PRINT, font(24, False), left + SIGN_W / 2, top + SIGN_H - 70, (90, 90, 96))

    # Room plate on the wall, mostly past the right edge of the frame.
    plate_left, plate_top = 1760, top + 30
    draw.rounded_rectangle(
        (plate_left, plate_top, plate_left + 330, plate_top + 120),
        radius=14,
        fill=(52, 58, 70),
    )
    draw.text((plate_left + 30, plate_top + 28), "Sala 204", font=font(54, True), fill=(236, 236, 240))
    return image, line_boxes


def centered(draw, text, face, center_x, y, color):
    """Draws text centered on center_x and returns its ink box."""
    box = draw.textbbox((0, 0), text, font=face)
    origin = (center_x - (box[2] - box[0]) / 2 - box[0], y)
    draw.text(origin, text, font=face, fill=color)
    return draw.textbbox(origin, text, font=face)


def smoothstep(edge0, edge1, t):
    x = min(max((t - edge0) / (edge1 - edge0), 0.0), 1.0)
    return x * x * (3 - 2 * x)


def camera(t):
    """Camera center (scene px), scale (output px per scene px), and roll (degrees) at time t."""
    cx, cy = SCENE_W / 2, SCENE_H / 2
    scale = 0.45
    roll = 0.0

    # Pan up and left, shake, zoom in while coming back, then drift.
    pan = smoothstep(1.1, 2.4, t)
    back = smoothstep(3.0, 4.1, t)
    cx += 120 * pan - 100 * back
    cy += 170 * pan - 230 * back
    scale *= 1 + 0.34 * smoothstep(3.0, 4.0, t) - 0.16 * smoothstep(4.1, 5.0, t)
    roll += 1.6 * smoothstep(4.0, 5.0, t)

    if 2.45 <= t <= 3.05:
        decay = math.exp(-(t - 2.45) * 4.5)
        cx += 46 * decay * math.sin((t - 2.45) * 2 * math.pi * 6.5)
        cy += 30 * decay * math.sin((t - 2.45) * 2 * math.pi * 5.0 + 1.1)

    # Hand tremor.
    cx += 6 * math.sin(2 * math.pi * 1.3 * t + 0.4) + 3 * math.sin(2 * math.pi * 3.1 * t + 2.0)
    cy += 5 * math.sin(2 * math.pi * 1.7 * t + 1.3) + 3 * math.sin(2 * math.pi * 2.6 * t + 0.2)
    roll += 0.35 * math.sin(2 * math.pi * 0.9 * t + 0.7)
    return cx, cy, scale, roll


def to_frame(t, x, y):
    """Where scene point (x, y) lands in the output frame at time t."""
    cx, cy, scale, roll = camera(t)
    r = math.radians(roll)
    dx, dy = x - cx, y - cy
    return (
        WIDTH / 2 + scale * (math.cos(r) * dx + math.sin(r) * dy),
        HEIGHT / 2 + scale * (-math.sin(r) * dx + math.cos(r) * dy),
    )


def glare(pixels, t):
    """A soft highlight that slides across the lower lines of the sign between 3.2 s and 4.4 s."""
    strength = math.sin(math.pi * min(max((t - 3.2) / 1.2, 0.0), 1.0))
    if strength <= 0:
        return pixels
    left = (SCENE_W - SIGN_W) / 2
    top = (SCENE_H - SIGN_H) / 2
    across = smoothstep(3.2, 4.4, t)
    u, v = to_frame(t, left + SIGN_W * (0.15 + 0.7 * across), top + SIGN_H * 0.62)
    scale = camera(t)[2]
    rows, cols = np.mgrid[0:HEIGHT, 0:WIDTH].astype(np.float32)
    falloff = np.exp(-(((cols - u) / (260 * scale)) ** 2 + ((rows - v) / (120 * scale)) ** 2))
    alpha = (0.93 * strength * falloff)[..., None]
    return pixels + alpha * (255 - pixels)


def view(source, t):
    cx, cy, scale, roll = camera(t)
    r = math.radians(roll)
    cos_r, sin_r = math.cos(r), math.sin(r)
    a, b = cos_r / scale, -sin_r / scale
    d, e = sin_r / scale, cos_r / scale
    c = cx - (a * WIDTH / 2 + b * HEIGHT / 2)
    f = cy - (d * WIDTH / 2 + e * HEIGHT / 2)
    return source.transform(
        (WIDTH, HEIGHT), Image.AFFINE, (a, b, c, d, e, f), resample=Image.BICUBIC
    )


def frame(source, index, rng):
    """One frame: five samples across a 180-degree shutter, averaged, softened, with sensor noise."""
    t = index / FPS
    samples = [
        np.asarray(view(source, t + (k / 4 - 0.5) / (2 * FPS)), dtype=np.float32) for k in range(5)
    ]
    lit = glare(np.mean(samples, axis=0), t)
    blurred = Image.fromarray(np.clip(lit, 0, 255).astype(np.uint8)).filter(
        ImageFilter.GaussianBlur(0.7)
    )
    noisy = np.asarray(blurred, dtype=np.float32) + rng.normal(0, 2.0, (HEIGHT, WIDTH, 3))
    return Image.fromarray(np.clip(noisy, 0, 255).astype(np.uint8))


def truth(line_boxes):
    """Where each sign line sits in every frame, in Vision-normalized space (origin bottom-left).

    Each box is centered on the line and sized along the line's own axes, so the
    camera's slight roll doesn't pad the height the way an axis-aligned box would.
    """
    frames = []
    for index in range(FPS * SECONDS):
        t = index / FPS
        scale = camera(t)[2]
        boxes = []
        for left, top, right, bottom in line_boxes:
            u, v = to_frame(t, (left + right) / 2, (top + bottom) / 2)
            width = (right - left) * scale / WIDTH
            height = (bottom - top) * scale / HEIGHT
            boxes.append([
                round(u / WIDTH - width / 2, 5),
                round(1 - v / HEIGHT - height / 2, 5),
                round(width, 5),
                round(height, 5),
            ])
        frames.append(boxes)
    return {
        "fps": FPS,
        "width": WIDTH,
        "height": HEIGHT,
        "lines": [text for text, *_ in LINES],
        "boxes": frames,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--out", type=pathlib.Path, default=DEFAULT_OUT)
    parser.add_argument("--frames", type=pathlib.Path, help="also write PNG frames here")
    args = parser.parse_args()

    source, line_boxes = scene()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    truth_path = args.out.with_suffix(".json")
    truth_path.write_text(json.dumps(truth(line_boxes), separators=(",", ":")) + "\n")
    rng = np.random.default_rng(11)
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = pathlib.Path(tmp)
        for index in range(FPS * SECONDS):
            frame(source, index, rng).save(tmp_dir / f"frame_{index:03d}.png")
        if args.frames:
            args.frames.mkdir(parents=True, exist_ok=True)
            for png in sorted(tmp_dir.glob("frame_*.png")):
                shutil.copy(png, args.frames / png.name)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            [
                "ffmpeg", "-y", "-loglevel", "error",
                "-framerate", str(FPS), "-i", str(tmp_dir / "frame_%03d.png"),
                "-c:v", "libx264", "-preset", "veryslow", "-crf", "26",
                "-pix_fmt", "yuv420p", "-movflags", "+faststart", "-an",
                str(args.out),
            ],
            check=True,
        )
    print(f"wrote {args.out} ({args.out.stat().st_size // 1024} KB) and {truth_path.name}")


if __name__ == "__main__":
    main()

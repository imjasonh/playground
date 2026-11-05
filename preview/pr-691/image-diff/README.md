# Image diff

Drop two images side by side and compare them in the browser. Matching
pixels stay as they are. The more a pixel differs, the more red it is
tinted.

Nothing is uploaded. Files are read locally and stay on your machine.

## Run locally

```bash
cd image-diff
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```

## How it compares

Different resolutions of the same aspect ratio are scaled to the larger
image, then compared pixel by pixel.

When the aspect ratios differ, the app builds a shared canvas whose
aspect is the geometric mean of the two, cover-crops both images to that
canvas (centered), and outlines the compared region on each source.
Cropped-away edges are dimmed so you can see what was left out.

The long edge is capped at 4096 pixels so large photos still compare
without locking the tab.

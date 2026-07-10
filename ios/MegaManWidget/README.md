# Mega Man Widget (Home Screen)

WidgetKit extension that plays Metal Man’s walk / throw / jump loop using the
public **timer-mask** animation technique (Bryce Bostwick —
[Apple’s Widget Backdoor](https://www.youtube.com/watch?v=NdJ_y1c_j_I)).

## Bundle ID

`io.github.imjasonh.playground.megamanwidget`

Apple requires a distinct Bundle ID for WidgetKit extensions. After this
extension lands on a machine that ships to TestFlight, run **iOS signing
bootstrap** once so match stores its App Store profile (same process as the
T9 keyboard).

## Requirements

- **Home Screen widget:** iOS 17+
- **In-app preview:** iOS 16+ (same animation view)

## Assets

- Metal Man frames sliced from `Shared/MegaManWidget/SourcesSheets/metal-man.gif`
  (walk / throw / jump / blade). Labeled slices:
  `SourcesSheets/metal-man-frames/`.
- Regenerate: `python3 ios/scripts/generate_megaman_sprites.py`
- Blink font: `Shared/MegaManWidget/Fonts/Custom-Regular.otf` from Bryce’s MIT
  [WidgetAnimation](https://github.com/brycebostwick/WidgetAnimation) sample.

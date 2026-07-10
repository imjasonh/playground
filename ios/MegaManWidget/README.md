# Mega Man Widget (Home Screen)

WidgetKit extension that plays a walk / jump / shoot sprite loop using the
public **timer-mask** animation technique (Bryce Bostwick —
[Apple’s Widget Backdoor](https://www.youtube.com/watch?v=NdJ_y1c_j_I)).

## Bundle ID

`io.github.imjasonh.playground.megamanwidget`

Apple requires a distinct Bundle ID for WidgetKit extensions. After this
extension lands on a machine that ships to TestFlight, run **iOS signing
bootstrap** once so match stores its App Store profile (same process as the
T9 keyboard).

## Requirements

- **Home Screen widget:** iOS 17+ (App Intent configuration for character pick)
- **In-app preview:** iOS 16+ (same animation view, local character picker)

## Character picker

Edit the widget (long-press → Edit Widget) to choose Mega Man or a Robot Master.
No App Group is required.

## Assets

- Sprites: original NES-style pixel art under
  `Shared/MegaManWidget/Assets.xcassets` (regenerate with
  `python3 ios/scripts/generate_megaman_sprites.py`).
- Blink font: `Shared/MegaManWidget/Fonts/Custom-Regular.otf` from Bryce’s MIT
  [WidgetAnimation](https://github.com/brycebostwick/WidgetAnimation) sample.

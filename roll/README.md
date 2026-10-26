# roll

Roll is the menu bar app. It puts one item in the menu bar and no Dock icon
or window. Click the die to roll. The icon changes to the face that came up.
When a countdown is set, the item also shows the days until the next date,
such as `30d`. Add later menu bar features here.

Right-click or Control-click for the menu. It lists each date as
`birthday (40 days)`, soonest first. Click a date, then confirm **Delete**,
to remove it. **New Countdown…** asks for a description and a date. The menu
also has **Check for Updates…** and **Quit Roll**.

**Take Monitor Photo** takes a screenshot of the display under the pointer and
makes it look like a phone photo of the monitor. It saves
`Monitor Photo <date> at <time>.jpg` on the Desktop and opens it. The filter
(`Sources/MonitorPhoto.swift`) simulates these effects:

- The phone is tilted, off-axis, and zoomed in a little, with lens barrel
  distortion. Screen edges can show the dark bezel.
- The screen's subpixel grid aliases against the sensor into colored moiré
  stripes.
- The image is defocused, more at the corners, and red and blue fringe apart.
- Black photographs as dark gray. Contrast and saturation drop, and the camera
  adds a white-balance cast.
- A room light reflects off the glass as a soft glare, and bright areas glow.
- The corners are darker, one side dims from the viewing angle, and dark areas
  show sensor noise.

Each photo picks new random values for these, so no two match. The first use
asks for Screen Recording access; after you allow it in System Settings, quit
and reopen Roll.

Bundle ID: `io.github.imjasonh.roll`

## Layout

```
roll/
├── project.yml
├── Roll.entitlements
├── Sources/
├── Tests/RollTests/
├── fastlane/
├── Gemfile
└── README.md
```

## Local development

Requires macOS and Xcode.

```bash
cd roll
brew install xcodegen
bundle install
xcodegen generate
open Roll.xcodeproj
```

To run the unit tests:

```bash
bundle exec fastlane test
```

## CI / releases

`.github/workflows/macos.yml` discovers changed macOS apps (top-level dirs whose
`project.yml` declares `platform: macOS`), runs `xcodegen` and `fastlane test` on
`macos-latest`, and on `main` with Developer ID and Sparkle secrets runs
`fastlane beta` (notarize and EdDSA-sign the ZIP) then publishes a GitHub Release
and Sparkle appcast on `gh-pages`.

- Design: [`docs/macos-sparkle-design.md`](../docs/macos-sparkle-design.md)
- Setup (certs, secrets, Sparkle keys): [`docs/macos-sparkle-setup.md`](../docs/macos-sparkle-setup.md)

Feed URL:

```text
https://imjasonh.github.io/playground/macos/roll/appcast.xml
```

In the running app, Control-click the menu bar die and choose **Check for Updates…**

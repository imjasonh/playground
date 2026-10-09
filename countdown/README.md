# Countdown

Menu bar countdowns for macOS. Countdown puts one item in the menu bar and no
Dock icon or window. The item shows how many days remain until the next date.
Click or right-click it to open the menu.

The menu lists each date as `birthday (40 days)`, soonest first. A date today
reads `(today)`. Click a date, then confirm **Delete**, to remove it. **New
Countdown…** asks for a description and a date. The menu bar shows that count
as `40d`, or `Today` when the next date is today. Dates you add stay on this
Mac until you delete them.

Bundle ID: `io.github.imjasonh.countdown`

## Layout

```
countdown/
├── project.yml
├── Countdown.entitlements
├── Sources/
├── Tests/CountdownTests/
├── fastlane/
├── Gemfile
└── README.md
```

## Local development

Requires macOS and Xcode.

```bash
cd countdown
brew install xcodegen
bundle install
xcodegen generate
open Countdown.xcodeproj
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
https://imjasonh.github.io/playground/macos/countdown/appcast.xml
```

In the running app, click the menu bar item and choose **Check for Updates…**

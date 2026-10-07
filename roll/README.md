# roll

Menu bar die for macOS. Roll puts one item in the menu bar and no Dock icon
or window. Click the die to roll. The icon changes to the face that came up.
Control-click or right-click for **Check for Updates…** and **Quit Roll**.

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

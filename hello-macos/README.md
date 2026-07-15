# hello-macos — Hello Mac

Minimal SwiftUI macOS sample app. Same role as the static [`hello/`](../hello/)
browser demo: a tiny end-to-end example of the **macOS app** type in this
playground (XcodeGen → test on a macOS runner → notarized Sparkle CD with
in-app **Check for Updates…**).

Bundle ID: `io.github.imjasonh.hello-macos`

## Layout

```
hello-macos/
├── project.yml              # XcodeGen spec (discovery marker: platform: macOS)
├── HelloMac.entitlements    # Hardened Runtime + Sparkle helpers
├── Sources/                 # SwiftUI app + SparkleUpdater
├── Tests/HelloMacTests/     # XCTest unit tests
├── fastlane/                # test + beta (Developer ID / notarize / sign_update)
├── Gemfile
└── README.md
```

## Local development

Requires macOS + Xcode.

```bash
cd hello-macos
brew install xcodegen
bundle install
xcodegen generate
open HelloMac.xcodeproj
# or:
bundle exec fastlane test
```

## CI / releases

`.github/workflows/macos.yml` discovers changed macOS apps (top-level dirs whose
`project.yml` declares `platform: macOS`), runs `xcodegen` + `fastlane test` on
`macos-latest`, and on `main` with Developer ID + Sparkle secrets runs
`fastlane beta` (notarize + EdDSA-sign the ZIP) then publishes a GitHub Release
+ Sparkle appcast on `gh-pages`.

- Design: [`docs/macos-sparkle-design.md`](../docs/macos-sparkle-design.md)
- Setup (certs / secrets / Sparkle keys): [`docs/macos-sparkle-setup.md`](../docs/macos-sparkle-setup.md)

Feed URL:

```text
https://imjasonh.github.io/playground/macos/hello-macos/appcast.xml
```

In the running app: **Hello Mac → Check for Updates…**

# hello-macos — Hello Mac

Minimal SwiftUI macOS sample app. Same role as the static [`hello/`](../hello/)
browser demo: a tiny end-to-end example of the **macOS app** type in this
playground (XcodeGen → test on a macOS runner → later Sparkle CD).

Bundle ID: `io.github.imjasonh.hello-macos`

## Layout

```
hello-macos/
├── project.yml          # XcodeGen spec (discovery marker: platform: macOS)
├── Sources/             # SwiftUI app
├── Tests/HelloMacTests/ # XCTest unit tests
├── fastlane/            # test lane (release lanes land in a follow-up)
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

## CI

`.github/workflows/macos.yml` discovers changed macOS apps (top-level dirs whose
`project.yml` declares `platform: macOS`), runs `xcodegen` + `fastlane test` on
`macos-latest`, and (once release secrets exist) will ship notarized Sparkle
updates from `main`. See [`docs/macos-sparkle-design.md`](../docs/macos-sparkle-design.md).

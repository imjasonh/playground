# hello-ios

A tiny SwiftUI temperature converter — the reference **iOS app** for this
playground, analogous to `hello/` for browser apps. It exists to exercise the
iOS CI pipeline end to end: real unit tests, real UI tests, and continuous
delivery to **TestFlight** on every push to `main`.

The interesting logic (`TemperatureConverter`, `ConverterViewModel`) lives
outside the views so it can be unit-tested without a simulator; the views carry
accessibility identifiers so the UI tests can drive them.

## Layout

```
hello-ios/
├── project.yml            # XcodeGen spec (source of truth + discovery marker)
├── Gemfile                # pins fastlane
├── fastlane/
│   ├── Fastfile           # lanes: test, beta (TestFlight)
│   ├── Appfile            # bundle identifier
│   └── Matchfile          # code-signing storage (fastlane match)
├── Sources/               # app + logic
│   ├── HelloIOSApp.swift
│   ├── ContentView.swift
│   ├── ConverterViewModel.swift
│   └── TemperatureConverter.swift
└── Tests/
    ├── HelloIOSTests/     # XCTest unit tests
    └── HelloIOSUITests/   # XCUITest UI tests
```

The generated `HelloIOS.xcodeproj` is git-ignored; regenerate it with XcodeGen.

## Prerequisites (macOS)

```bash
brew install xcodegen        # project generation
bundle install               # fastlane (from the Gemfile)
```

## Generate the Xcode project

```bash
cd hello-ios
xcodegen generate
open HelloIOS.xcodeproj      # optional, to work in Xcode
```

## Run tests

```bash
# via fastlane (what CI runs)
bundle exec fastlane test

# or directly with xcodebuild
xcodebuild test \
  -project HelloIOS.xcodeproj \
  -scheme HelloIOS \
  -destination 'platform=iOS Simulator,name=iPhone 15,OS=latest'
```

## Ship to TestFlight

CI does this automatically on push to `main` (see `.github/workflows/ios.yml`).
To run it locally you need the signing/App Store Connect environment described
below:

```bash
bundle exec fastlane beta
```

### Required environment / secrets

The `beta` lane needs these (configured as GitHub Actions secrets for CI):

| Variable | What it is |
|----------|------------|
| `ASC_KEY_ID` | App Store Connect API key ID |
| `ASC_ISSUER_ID` | App Store Connect API issuer ID |
| `ASC_API_KEY_P8` | The `.p8` private key contents, **base64-encoded** |
| `MATCH_GIT_URL` | Private git repo holding `match` certs/profiles |
| `MATCH_PASSWORD` | Passphrase that decrypts the `match` repo |
| `MATCH_GIT_BASIC_AUTHORIZATION` | Base64 `user:token` to read the match repo (or a deploy key) |

Until these exist, CI still runs the full test suite and simply **skips** the
TestFlight upload. See [`docs/ios-testflight-design.md`](../docs/ios-testflight-design.md)
for the end-to-end design and the one-time Apple-side setup checklist.

# Design: macOS apps with Sparkle CD

> **Status:** discovery + test CI for macOS apps is implemented (`hello-macos/`,
> `macos.yml`). **Release plumbing** (`fastlane beta`, `publish-macos-sparkle.sh`,
> setup guide) is in-repo; shipping activates once Developer ID / Sparkle secrets
> exist (see [`macos-sparkle-setup.md`](macos-sparkle-setup.md)). Until then,
> pushes to `main` test only and warn that ship was skipped — same pattern as iOS
> TestFlight without ASC secrets.
>
> **Still follow-up:** embed the Sparkle framework + `SUPublicEDKey` in the app
> after generating keys (setup Step 3–4), so installed builds auto-check the
> appcast. Packaging + notarization + appcast publish do not require that yet.

## 1. Goals & how they map to what we already do

| Today | macOS equivalent |
|-------|------------------|
| Browser → GitHub Pages | DMG/ZIP + `appcast.xml` on Pages / Releases |
| iOS → TestFlight on `main` | macOS → notarize + Sparkle feed on `main` |
| Marker: `index.html` / `go.mod` / iOS `project.yml` (`platform: iOS`) | Marker: `project.yml` with `platform: macOS` |
| `ios.yml` on `macos-latest` | `macos.yml` on `macos-latest` |

**Why not Mac TestFlight for v1?** Mac TestFlight requires Mac App Store
sandboxing. Diagnostic / system tools (and even a simple Hello scaffold we may
later extend) are a better fit for **Developer ID + notarization + Sparkle**,
which gives continuous in-app updates without the sandbox. Sparkle is free;
we host the feed ourselves.

## 2. Repo conventions

A **macOS app** is a non-hidden top-level directory whose `project.yml` declares
at least one XcodeGen target with `platform: macOS`. iOS apps also use
`project.yml` but declare `platform: iOS` — discovery scripts distinguish them
by that line (see `discover-macos-apps.sh` / `discover-ios-apps.sh`).

Unlike iOS (exactly one Playground host), **many macOS apps are allowed**, each
its own top-level directory and Bundle ID. Do **not** fold macOS apps into
`ios/`.

```
hello-macos/
├── project.yml            # XcodeGen spec (discovery marker)
├── Sources/
├── Tests/
├── fastlane/              # lanes: test, (later) beta
├── Gemfile
├── README.md
└── .gitignore
```

Rules:

- Isolated: own `project.yml`, `fastlane/`, Bundle ID. No repo-root Xcode workspace.
- No `index.html` — not a Pages browser app (the *appcast* may live on gh-pages).
- Do not commit `*.xcodeproj`, `DerivedData/`, `*.dmg`, `*.xcarchive`, signing material.
- Bundle IDs: `io.github.imjasonh.<app>` (e.g. `io.github.imjasonh.hello-macos`).

## 3. Continuous delivery

On push to `main` when a macOS app changed **and** `MACOS_DEVELOPER_ID_P12` is
present, `macos-ci.sh` runs:

1. `xcodegen generate` → `fastlane test`
2. `fastlane beta` — Developer ID sign → notarize (`notarytool` via ASC API key)
   → staple → ZIP enclosure + `sparkle-metadata.json`
3. `publish-macos-sparkle.sh` — GitHub Release asset + rewrite
   `gh-pages/macos/<app>/appcast.xml`

Click-by-click secrets setup: [`macos-sparkle-setup.md`](macos-sparkle-setup.md).

Suggested feed URL shape:

```text
https://imjasonh.github.io/playground/macos/hello-macos/appcast.xml
```

### Secrets

| Secret | Purpose |
|--------|---------|
| `MACOS_DEVELOPER_ID_P12` | Base64 Developer ID Application certificate |
| `MACOS_DEVELOPER_ID_PASSWORD` | Password for that `.p12` |
| `SPARKLE_EDDSA_PRIVATE_KEY` | Sparkle Ed25519 private key (optional until in-app Sparkle ships) |
| Existing `ASC_*` / `APPLE_TEAM_ID` | Notarization via App Store Connect API key |

Without `MACOS_DEVELOPER_ID_P12`, `macos.yml` tests and prints the skip warning.

## 4. User updates (Sparkle)

- Sparkle is **free** (open source); no SaaS fee.
- App embeds Sparkle + public EdDSA key + `SUFeedURL` pointing at the Pages appcast.
- On each `main` ship, CI appends an appcast item; the installed app checks the
  feed (background / on launch) and applies updates — the closest analog to
  TestFlight auto-updates for a non–Mac App Store app.
- Diagnosis / offline use: a **stapled** build launches offline; checking for
  updates needs network once.

## 5. PR previews

No frictionless Mac install link. Baseline: CI tests on PRs. Optional later:
upload a notarized (or ad-hoc) PR build as a workflow artifact. Prefer shipping
continuous updates from `main` only.

## 6. Adding another macOS app

1. Create a top-level dir with `project.yml` (`platform: macOS`).
2. Add `fastlane test` (and eventually `beta`).
3. Open a PR — `macos.yml` picks it up automatically once discovery sees
   `platform: macOS`. No workflow edits required for the test path.

Reference implementation: [`hello-macos/`](../hello-macos/).

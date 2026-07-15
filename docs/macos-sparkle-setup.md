# macOS Sparkle setup: certs, notarization, and continuous updates

This is the click-by-click companion to
[`macos-sparkle-design.md`](macos-sparkle-design.md). After this is done once,
`macos.yml` on push to `main` can notarize a changed macOS app and publish a
Sparkle appcast — the closest analog to iOS TestFlight auto-updates for a
non–Mac App Store app.

Until Developer ID secrets exist, CI still **tests** macOS apps and prints
`macOS release skipped` (same idea as TestFlight without ASC secrets). Once
Developer ID is configured, release also requires `SPARKLE_EDDSA_PRIVATE_KEY`
(the app embeds `SUPublicEDKey` and will reject unsigned enclosures).

## What you need

- Apple Developer Program membership (you already have this for iOS TestFlight)
- A **Developer ID Application** certificate (not Apple Distribution — that one
  is for App Store / TestFlight)
- Ability to add GitHub Actions secrets on this repo
- ~15 minutes

## Step 1 — Create a Developer ID Application certificate

1. Open [developer.apple.com/account/resources/certificates](https://developer.apple.com/account/resources/certificates/list).
2. **+** → **Developer ID Application** → continue.
3. Create a CSR from Keychain Access on a Mac (*Keychain Access → Certificate
   Assistant → Request a Certificate From a Certificate Authority*), upload it,
   download the `.cer`.
4. Double-click the `.cer` to install it in Keychain.
5. In Keychain Access, select the **Developer ID Application** cert + private
   key → right-click → **Export 2 items…** → save as `developer-id.p12` with a
   strong password.

Keep the `.p12` and password offline; CI only needs the base64 form (next step).

## Step 2 — Add signing / notarization secrets

In the GitHub repo → **Settings → Secrets and variables → Actions**:

| Secret | Value |
|--------|--------|
| `MACOS_DEVELOPER_ID_P12` | `base64 -i developer-id.p12 \| pbcopy` (Mac) or `base64 -w0 developer-id.p12` (Linux) |
| `MACOS_DEVELOPER_ID_PASSWORD` | Password you set on the `.p12` |
| `APPLE_TEAM_ID` | Already used by iOS CI — reuse it |
| `ASC_KEY_ID` / `ASC_ISSUER_ID` / `ASC_API_KEY_P8` | Already used for TestFlight — reused for `notarytool` |

## Step 3 — Sparkle EdDSA keypair

`hello-macos` already embeds the public key (`SUPublicEDKey` in `project.yml`)
and wires Sparkle (`SPUStandardUpdaterController` + **Check for Updates…**).
CI signs each ZIP enclosure with the matching private seed.

### If you are continuing the existing hello-macos key

Add the repo secret `SPARKLE_EDDSA_PRIVATE_KEY` to the **base64 seed** that
matches the checked-in public key
`pFvSb5Quq/HBMc9EvhTTD5zbctf7MCuAks0mXaZiZW0=`. That seed is Sparkle’s
“new format”: **base64 of 32 raw bytes** (one line, no PEM headers). Never
commit it.

### If you need a fresh keypair (new app or rotation)

On a Mac with Sparkle’s binary tools (from a
[Sparkle release](https://github.com/sparkle-project/Sparkle/releases) tarball):

```bash
./bin/generate_keys
# Prints the public key; also stores the private seed for sign_update.
# To export the private seed string for GitHub Actions:
./bin/generate_keys -x   # or copy from Keychain / the tool’s output
```

Sparkle 2’s preferred CI secret is the **new-format seed** (base64), not a PEM
file. Put that string in `SPARKLE_EDDSA_PRIVATE_KEY`. Put the matching public
key into the app’s `project.yml` under `info.properties`:

```yaml
SUFeedURL: "https://imjasonh.github.io/playground/macos/<app>/appcast.xml"
SUPublicEDKey: "<paste public key here>"
SUEnableAutomaticChecks: true
```

Never commit the private seed. Rotating the key requires shipping a new app
build that embeds the new public key — old installs keep verifying with the
key baked into their binary.

## Step 4 — Embed Sparkle in the app

For `hello-macos/` this is already done. For a new macOS app:

1. Add the Sparkle Swift package + product dependency in `project.yml`.
2. Set `SUFeedURL` / `SUPublicEDKey` as above (must live in `project.yml` —
   XcodeGen regenerates Info.plist and will strip hand-edits).
3. Allow Sparkle’s helpers under Hardened Runtime
   (`com.apple.security.cs.disable-library-validation` in entitlements).
4. Create an `SPUStandardUpdaterController` (see
   `hello-macos/Sources/SparkleUpdater.swift`) and a **Check for Updates…**
   menu command.

The **feed URL** shape we use:

```text
https://imjasonh.github.io/playground/macos/<app-name>/appcast.xml
```

Binaries (ZIP enclosures) are attached to **GitHub Releases**; the appcast on
Pages points at those asset URLs. Sparkle itself is free — hosting is existing
Pages + Releases.

## Step 5 — Verify end-to-end

1. Confirm `SPARKLE_EDDSA_PRIVATE_KEY` is set (and matches `SUPublicEDKey`).
2. Merge a change under `hello-macos/` to `main` (or bump
   `MARKETING_VERSION` / `CURRENT_PROJECT_VERSION`).
3. Watch the **macOS** workflow: test → `fastlane beta` → notarize → publish.
4. Confirm:
   - A GitHub Release asset for the new version (e.g. `HelloMac-1.0.6.zip`)
   - `https://imjasonh.github.io/playground/macos/hello-macos/appcast.xml`
     lists that version with `sparkle:edSignature`
5. Install an older build, open **Hello Mac → Check for Updates…**, and confirm
   Sparkle offers the new version.

## Troubleshooting

| Symptom | Likely cause |
|---------|----------------|
| `macOS release skipped` warning | `MACOS_DEVELOPER_ID_P12` not set |
| `Missing release secrets: SPARKLE_EDDSA_PRIVATE_KEY` | Secret not added (required once Sparkle is embedded) |
| Gatekeeper blocks the app | Notarization failed or ticket not stapled |
| Notarization Invalid after adding Sparkle | Nested Sparkle XPC/Autoupdate not re-signed with your Developer ID; CI re-signs them in `fastlane beta` and prints `notarytool log` on failure |
| Sparkle says signature invalid | Wrong / rotated EdDSA private key vs `SUPublicEDKey` |
| Appcast 404 | Pages publish step didn't run or path mismatch |
| `notarytool` auth error | ASC API key secrets missing or wrong team |
| App crashes / Sparkle helpers blocked | Missing `disable-library-validation` entitlement |

## Security reminders

- Do **not** commit `.p12`, Sparkle private seeds, or `*.pem` key files.
- Rotate the Sparkle key only if you also ship a new app build with the matching
  public key — old installs verify with the key baked into their binary.

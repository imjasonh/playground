# macOS Sparkle setup: certs, notarization, and continuous updates

This is the click-by-click companion to
[`macos-sparkle-design.md`](macos-sparkle-design.md). After this is done once,
`macos.yml` on push to `main` can notarize a changed macOS app and publish a
Sparkle appcast — the closest analog to iOS TestFlight auto-updates for a
non–Mac App Store app.

Until these secrets exist, CI still **tests** macOS apps and prints
`macOS release skipped` (same idea as TestFlight without ASC secrets).

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

## Step 3 — Generate a Sparkle EdDSA keypair

On a Mac with a Sparkle release checkout (or the `Sparkle` binary tools):

```bash
# From a Sparkle 2 distribution, or after resolving the SPM package once:
./bin/generate_keys
# For CI, also write the private key to a file (do not commit it):
./bin/generate_keys -f sparkle_eddsa_private.pem
```

`generate_keys` prints a **public** key string. Put that into each macOS app's
`project.yml` under `info.properties`:

```yaml
SUFeedURL: "https://imjasonh.github.io/playground/macos/<app>/appcast.xml"
SUPublicEDKey: "<paste public key here>"
```

Add the **private** key file contents as the repo secret
`SPARKLE_EDDSA_PRIVATE_KEY` (the whole PEM / key file body). Never commit it.

## Step 4 — Embed Sparkle in the app (when keys exist)

For `hello-macos/` (and later apps):

1. Add the Sparkle Swift package + product dependency in `project.yml`.
2. Set `SUFeedURL` / `SUPublicEDKey` as above (must live in `project.yml` —
   XcodeGen regenerates Info.plist and will strip hand-edits).
3. Create an `SPUStandardUpdaterController` in the SwiftUI app (or AppKit
   delegate) so check-for-updates runs.

The **feed URL** shape we use:

```text
https://imjasonh.github.io/playground/macos/<app-name>/appcast.xml
```

Binaries (DMGs) are attached to **GitHub Releases**; the appcast on Pages points
at those asset URLs. Sparkle itself is free — hosting is existing Pages +
Releases.

## Step 5 — Verify end-to-end

1. Merge a change under `hello-macos/` to `main` (or bump
   `CURRENT_PROJECT_VERSION`).
2. Watch the **macOS** workflow: test → `fastlane beta` → notarize → publish.
3. Confirm:
   - A GitHub Release (or release asset) for the new version
   - `https://imjasonh.github.io/playground/macos/hello-macos/appcast.xml`
     lists that version with a Sparkle `edSignature`
4. Install the DMG once, bump the version again, confirm Sparkle offers the
   update (or use the app's **Check for Updates** menu).

## Troubleshooting

| Symptom | Likely cause |
|---------|----------------|
| `macOS release skipped` warning | `MACOS_DEVELOPER_ID_P12` not set |
| Gatekeeper blocks the app | Notarization failed or ticket not stapled |
| Sparkle says signature invalid | Wrong / rotated EdDSA private key vs `SUPublicEDKey` |
| Appcast 404 | Pages publish step didn't run or path mismatch |
| `notarytool` auth error | ASC API key secrets missing or wrong team |

## Security reminders

- Do **not** commit `.p12`, Sparkle private keys, or `*.pem` key files.
- Rotate the Sparkle key only if you also ship a new app build with the matching
  public key — old installs verify with the key baked into their binary.

# T9 Multi-tap — Custom Keyboard extension

System keyboard for old Nokia-style multi-tap.
Bundle ID: `io.github.imjasonh.playground.t9keyboard` (**required by Apple** —
extensions cannot use the host app id).

Shared engine: [`../Shared/T9/`](../Shared/T9/). In-app demo (host Bundle ID):
`Sources/Experiments/T9Keyboard/`.

## Enable

Settings → General → Keyboard → Keyboards → Add New Keyboard… → **T9 Multi-tap**.

## Signing

Listed in `fastlane/Matchfile`. After this extension was added, run **iOS
signing bootstrap** once (creates Bundle ID if missing + App Store profile).
Later **in-app** experiments do not need bootstrap — see [`../AGENTS.md`](../AGENTS.md).

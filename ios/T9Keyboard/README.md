# T9 Multi-tap — Custom Keyboard extension

Old Nokia-style **multi-tap** keyboard embedded in the Playground app
(`io.github.imjasonh.playground.t9keyboard`).

Tap a key repeatedly to cycle its letters; wait ~1s or tap another key to
commit. Shared engine + pad UI live in [`../Shared/T9/`](../Shared/T9/).

## How it works

| Input | Behavior |
|-------|----------|
| Tap `2`–`9` | Cycle letters (and the digit) for that key |
| Tap `1` | Cycle punctuation / `1` |
| Tap `0` | Cycle space / `0` |
| Long-press a digit | Insert that digit immediately |
| `*` | Cycle shift: `abc` → `Abc` → `ABC` → `123` |
| `#` | Insert a space |
| Delete | Cancel pending letter, or delete last committed character |
| Return | Commit pending, then insert newline |
| Globe | System next-keyboard switcher |

## Enable on a device

1. Install Playground (TestFlight or local run).
2. **Settings → General → Keyboard → Keyboards → Add New Keyboard…**
3. Choose **T9 Multi-tap** under Third-Party Keyboards.
4. In any text field, hold the **globe** key and select it.

The in-app **T9 Keyboard** experiment (host app) has the same pad for Simulator
practice and a shortcut to open Settings.

## Bundle / signing

| | |
|--|--|
| Display name | T9 Multi-tap |
| Bundle ID | `io.github.imjasonh.playground.t9keyboard` |
| Open access | Off (sandboxed; no network / shared container) |
| Principal class | `KeyboardViewController` |

Needs its own App ID + App Store profile. See the host
[`../README.md`](../README.md) and [`../../docs/ios-testflight-setup.md`](../../docs/ios-testflight-setup.md)
(Step 3b / signing bootstrap).

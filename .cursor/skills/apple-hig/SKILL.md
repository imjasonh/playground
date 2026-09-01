---
name: apple-hig
description: >-
  Consult Apple's Human Interface Guidelines when designing or editing iOS,
  iPadOS, macOS, watchOS, or visionOS UI (SwiftUI or UIKit). Use for
  accessibility labels, hit targets, Dynamic Type, empty states, buttons,
  navigation, SF Symbols, Dark Mode, feedback, and platform controls. Also
  trigger when reviewing Apple app UI, VoiceOver issues, or "does this feel
  native?"
---

# Apple Human Interface Guidelines

Apply the [Human Interface Guidelines](https://developer.apple.com/design/human-interface-guidelines/)
when you design, edit, or review Apple-platform UI in this repository
(`ios/`, `hello-macos/`, `onramp/`, and any future Apple apps).

This skill is a working subset for playground apps. When this file does not
cover a question, open the linked HIG topic and follow Apple's guidance. Prefer
system controls and patterns over custom chrome unless the experiment *is* the
custom chrome (for example Doom Face's intentional game aesthetic).

## When to use

Read this skill before you:

- Add or change SwiftUI / UIKit views in `ios/`, `hello-macos/`, or `onramp/`
- Add icon-only buttons, toolbars, composers, or camera chrome
- Ship empty lists, selection placeholders, or error gates
- Touch accessibility identifiers, VoiceOver labels, or Dynamic Type
- Choose colors, materials, or forced light/dark backgrounds

Also use it for PR review of Apple UI. Do not rewrite unrelated screens just to
chase HIG purity; fix what you are already changing, plus nearby high-impact
gaps (unlabeled icon buttons, undersized hit targets, bare empty states).

## Source priority

1. Product rules for the app (`ios/AGENTS.md`, `onramp/AGENTS.md`, app README).
2. Platform APIs and patterns already used in that directory.
3. This skill and the official HIG topic linked for the issue.
4. [UI Design Dos and Don'ts](https://developer.apple.com/design/tips/) for the
   quick visual checklist.

## Consult the right HIG page

| Situation | Start here |
| --- | --- |
| VoiceOver, labels, Dynamic Type, control size | [Accessibility](https://developer.apple.com/design/human-interface-guidelines/accessibility) |
| Buttons, destructive actions, toolbars | [Buttons](https://developer.apple.com/design/human-interface-guidelines/buttons) |
| Safe areas, hierarchy, adaptation | [Layout](https://developer.apple.com/design/human-interface-guidelines/layout) |
| Empty lists / missing content | [Empty views](https://developer.apple.com/design/human-interface-guidelines/empty-views) (and `ContentUnavailableView` on iOS 17+ / macOS 14+) |
| SF Symbols, variants, a11y text | [SF Symbols](https://developer.apple.com/design/human-interface-guidelines/sf-symbols) |
| Color, Dark Mode, contrast | [Color](https://developer.apple.com/design/human-interface-guidelines/color) |
| Text sizing and styles | [Typography](https://developer.apple.com/design/human-interface-guidelines/typography) |
| Feedback after copy / success | [Feedback](https://developer.apple.com/design/human-interface-guidelines/feedback) |
| Quick hit-target / contrast checklist | [Dos and Don'ts](https://developer.apple.com/design/tips/) |

Fetch or open the linked page when the decision is non-obvious. Do not invent
platform rules that contradict Apple.

## Non-negotiable checklist

Run this before you call Apple UI done:

1. **Every interactive control has a name.** Icon-only buttons need
   `.accessibilityLabel` (SwiftUI) or `accessibilityLabel` (UIKit). `.help` and
   `accessibilityIdentifier` are not substitutes for a spoken name.
2. **Hit targets meet platform minima.** iPhone/iPad: aim for **44×44 pt**
   ([tips](https://developer.apple.com/design/tips/); HIG default control size).
   Visual glyph can be smaller inside a larger tappable frame. macOS default
   control size is 28×28 pt.
3. **Text uses Dynamic Type text styles** (`.body`, `.headline`, `.caption`, …)
   or `@ScaledMetric` / `UIFontMetrics`. Avoid fixed `.system(size:)` for
   primary UI chrome unless the surface is intentionally fixed (game HUD).
4. **Empty states explain what is missing and what to do next.** Prefer
   `ContentUnavailableView` when the deployment target allows it; otherwise use
   an SF Symbol + title + short description with the same content.
5. **Prefer platform controls.** Use `Button`, `Toggle`, `Slider`, `Label`,
   `NavigationStack` / `NavigationSplitView`, `TabView` instead of reinventing
   checkboxes or chrome.
6. **Do not convey meaning with color alone.** Pair color with text, symbol
   variant, or an accessibility value ("2.1 g, elevated").
7. **Respect appearance.** Prefer semantic colors
   (`Color.primary`, `Color(.systemBackground)`, materials) over hardcoded RGB
   unless the experience requires a fixed theme.
8. **Confirm destructive or mutating actions.** Use `role: .destructive` and a
   confirmation dialog when the action deletes data or changes the system.
9. **Acknowledge success.** After copy-to-pasteboard or similar silent actions,
   give brief feedback (status text, `NSSound`, or equivalent).
10. **Hide decorative images from VoiceOver.** Use `.accessibilityHidden(true)`
    on icons that duplicate adjacent text.

## Accessibility labels

HIG: assistive technologies need accurate labels so people can understand and
operate controls.

| Pattern | Do | Don't |
| --- | --- | --- |
| Icon-only button | `.accessibilityLabel("Send")` | Rely on SF Symbol name alone |
| Toggle / mode | Label the **action or next state** ("Switch to front camera") | Label only the current state ("Front camera") without a hint |
| Selected control | Keep the name; add `.accessibilityAddTraits(.isSelected)` | Change the spoken name to "Selected …" only |
| Value control | `.accessibilityLabel("Sensitivity")` + `.accessibilityValue("60%")` | Identifier without label/value |
| Composite row | `.accessibilityElement(children: .combine)` or one explicit label | Orphan icon + unlabeled text siblings |

```swift
Button { send() } label: {
    Image(systemName: "arrow.up.circle.fill")
}
.accessibilityLabel("Send")
.accessibilityIdentifier("sendButton") // tests only; not VoiceOver

Button { session.flipCamera() } label: {
    Image(systemName: "arrow.triangle.2.circlepath.camera")
}
.accessibilityLabel(
    session.usingFrontCamera ? "Switch to rear camera" : "Switch to front camera"
)
```

## Hit targets and layout

From [Accessibility](https://developer.apple.com/design/human-interface-guidelines/accessibility)
and [Dos and Don'ts](https://developer.apple.com/design/tips/):

| Platform | Default control size | Absolute minimum |
| --- | --- | --- |
| iOS, iPadOS | 44×44 pt | 28×28 pt |
| macOS | 28×28 pt | 20×20 pt |
| watchOS | 44×44 pt | 28×28 pt |

```swift
Image(systemName: "xmark")
    .frame(width: 24, height: 24)
    .frame(minWidth: 44, minHeight: 44) // tappable area
    .contentShape(Rectangle())
```

Keep related controls near the content they affect. Respect safe areas. Avoid
crowding unrelated controls; group with spacing or materials
([Layout](https://developer.apple.com/design/human-interface-guidelines/layout)).

## Dynamic Type and typography

- Prefer text styles: `.largeTitle`, `.title`, `.headline`, `.body`, `.callout`,
  `.subheadline`, `.footnote`, `.caption`, `.caption2`.
- Scale custom sizes with `@ScaledMetric` or `UIFontMetrics`.
- Allow text to grow; use `.lineLimit` + truncation only when the layout truly
  cannot reflow (dense lists). Test at the largest accessibility sizes.
- Body text should stay legible; HIG minimums are about **11 pt** on iOS and
  **10 pt** on macOS — do not ship UI below that.

## Empty views

Empty views should not feel like a broken screen. State what is empty, why it
matters, and the next step when there is one.

```swift
// macOS 14+ / iOS 17+
ContentUnavailableView(
    "No rides yet",
    systemImage: "bicycle",
    description: Text("Record a ride from the Ride Monitor tab.")
)

// iOS 16-compatible equivalent
VStack(spacing: 8) {
    Image(systemName: "bicycle")
        .font(.largeTitle)
        .foregroundStyle(.secondary)
        .accessibilityHidden(true)
    Text("No rides yet")
        .font(.headline)
    Text("Record a ride from the Ride Monitor tab.")
        .font(.subheadline)
        .foregroundStyle(.secondary)
        .multilineTextAlignment(.center)
}
.frame(maxWidth: .infinity)
.padding()
```

Use the same pattern for split-view "nothing selected" panes.

## Buttons, toggles, and destructive actions

- Prefer `Label("Title", systemImage:)` so title and symbol stay paired for
  VoiceOver.
- Use `.borderedProminent` for the single primary action in a region; keep
  secondary actions quieter.
- Mark delete/stop/wipe with `role: .destructive`. Confirm when the action is
  hard to undo.
- Prefer `Toggle` over custom checkbox glyph buttons unless you need a
  non-switch control and then expose selected traits yourself.

## Color, symbols, and appearance

- Use SF Symbols with system rendering so they track Dynamic Type and appearance
  ([SF Symbols](https://developer.apple.com/design/human-interface-guidelines/sf-symbols)).
- Prefer fill / slash / enclosed variants to show state instead of inventing
  new metaphors.
- Provide accessibility text for any custom symbol.
- Hardcoded light-only or dark-only backgrounds need an explicit product reason
  (immersive camera, game). Still keep contrast high and avoid relying on color
  alone for status.

## Feedback

After an action whose result is otherwise invisible (copy, save, export):

- Show a short status string ("Copied"), a checkmark that reverts, or play the
  system feedback sound on Mac.
- Disable or busy-state the control while work runs; restore when finished.
- Progress that updates should remain reachable to VoiceOver (do not trap focus
  in a non-updating region).

## Playground-specific notes

| App | Deployment | Notes |
| --- | --- | --- |
| `ios/` | iOS 16.2 | No `ContentUnavailableView` without availability checks; keep UI-test `accessibilityIdentifier`s; experiments share one host Bundle ID |
| `onramp/` | macOS 14 | `ContentUnavailableView` OK; confirm-before-run for `SuggestedAction` is already correct — do not weaken it |
| `hello-macos/` | macOS 13 | Keep the sample minimal; still label headers and avoid hardcoded version strings when `Bundle` has them |

Match neighboring SwiftUI style in each app. Do not introduce a design system
or shared UI kit across Apple apps unless maintainers ask for one.

## PR and review bar

When a change touches Apple UI, the PR description should note HIG-relevant
fixes (labels, targets, empty states, Dynamic Type) in plain language. Do not
cite every HIG URL. If you skipped a known gap on purpose (fixed theme, game
HUD), say why.

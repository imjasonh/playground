import AppKit
import SwiftUI

/// Full-window gate: hard block on unsupported OS/device, aggressive setup when
/// Apple Intelligence is off or the on-device model is still downloading.
struct FoundationModelsGateView: View {
    @ObservedObject var gate: FoundationModelsGateModel

    var body: some View {
        Group {
            switch gate.status {
            case .checking:
                checkingPane
            case .available:
                EmptyView()
            case .needsAppleIntelligenceEnabled:
                setupPane(kind: .enable)
            case .modelNotReady:
                setupPane(kind: .download)
            case .unsupportedOperatingSystem:
                hardBlockPane(kind: .unsupportedOS)
            case .deviceNotEligible:
                hardBlockPane(kind: .deviceNotEligible)
            case .unavailableOther(let detail):
                hardBlockPane(kind: .other(detail))
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityIdentifier("foundation-models-gate")
    }

    private var checkingPane: some View {
        VStack(spacing: 16) {
            ProgressView()
                .controlSize(.large)
            Text("Checking Apple Intelligence…")
                .font(.title2.weight(.semibold))
            Text("Onramp needs the on-device Foundation Model to triage.")
                .foregroundStyle(.secondary)
        }
        .padding(40)
    }

    private enum SetupKind {
        case enable
        case download
    }

    private func setupPane(kind: SetupKind) -> some View {
        VStack(spacing: 0) {
            Spacer(minLength: 24)
            VStack(spacing: 20) {
                Image(systemName: kind == .download ? "arrow.down.circle.fill" : "apple.logo")
                    .font(.system(size: 64))
                    .foregroundStyle(.tint)
                    .accessibilityHidden(true)

                Text(kind == .download
                     ? "Download the on-device model"
                     : "Turn on Apple Intelligence")
                    .font(.largeTitle.weight(.bold))
                    .multilineTextAlignment(.center)

                Text(kind == .download
                     ? "Apple Intelligence is on, but the Foundation Model isn’t ready yet. Onramp can’t triage until the download finishes — keep power plugged in and this window open."
                     : "Onramp is built around Apple’s on-device Foundation Model. Until Apple Intelligence is enabled (and the model finishes downloading), Chat won’t work and triage is incomplete.")
                    .font(.title3)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: 520)

                if kind == .download {
                    ProgressView()
                        .controlSize(.regular)
                        .padding(.top, 4)
                    Text("Checking every few seconds…")
                        .font(.callout)
                        .foregroundStyle(.secondary)
                }

                VStack(spacing: 12) {
                    Button {
                        gate.openSettingsAndRefresh()
                    } label: {
                        Text(kind == .download
                             ? "Open Apple Intelligence Settings"
                             : "Enable Apple Intelligence…")
                            .frame(maxWidth: 360)
                    }
                    .buttonStyle(.borderedProminent)
                    .controlSize(.large)
                    .keyboardShortcut(.defaultAction)
                    .accessibilityIdentifier("gate-open-settings")

                    Button("I’ve enabled it — check again") {
                        gate.refresh()
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.large)
                    .accessibilityIdentifier("gate-check-again")
                }
                .padding(.top, 8)

                Text(kind == .download
                     ? "Model downloads can take several minutes. Leave the Mac awake."
                     : "After enabling, macOS may download model assets in the background.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: 420)
            }
            .padding(40)

            Spacer(minLength: 24)

            // Escape hatch only for temporary setup — not for unsupported OS.
            Button("Continue with Playbooks only (no Chat)") {
                gate.continueWithPlaybooksOnly()
            }
            .buttonStyle(.plain)
            .font(.callout)
            .foregroundStyle(.secondary)
            .padding(.bottom, 28)
            .accessibilityIdentifier("gate-playbooks-only")
        }
        .background(Color(nsColor: .windowBackgroundColor))
    }

    private enum HardBlockKind {
        case unsupportedOS
        case deviceNotEligible
        case other(String)
    }

    private func hardBlockPane(kind: HardBlockKind) -> some View {
        VStack(spacing: 20) {
            Image(systemName: "xmark.octagon.fill")
                .font(.system(size: 72))
                .foregroundStyle(.red)
                .accessibilityHidden(true)

            Text("Onramp can’t run on this Mac")
                .font(.largeTitle.weight(.bold))
                .multilineTextAlignment(.center)

            Text(hardBlockMessage(kind))
                .font(.title3)
                .foregroundStyle(.primary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: 540)

            Text(hardBlockDetail(kind))
                .font(.body)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: 480)

            Text("This is a hard requirement — there is no workaround inside the app.")
                .font(.headline)
                .foregroundStyle(.red)
                .multilineTextAlignment(.center)
                .padding(.top, 8)
                .accessibilityIdentifier("gate-hard-block-banner")
        }
        .padding(48)
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .background(Color.red.opacity(0.06))
        .accessibilityIdentifier("gate-hard-block")
    }

    private func hardBlockMessage(_ kind: HardBlockKind) -> String {
        switch kind {
        case .unsupportedOS:
            return "macOS 26 or later with Apple Intelligence is required."
        case .deviceNotEligible:
            return "This Mac isn’t eligible for Apple Intelligence."
        case .other:
            return "Apple’s on-device Foundation Model isn’t available here."
        }
    }

    private func hardBlockDetail(_ kind: HardBlockKind) -> String {
        switch kind {
        case .unsupportedOS:
            return "Onramp uses Apple Foundation Models for triage. Upgrade to a supported macOS release on Apple Intelligence–capable hardware, then reopen Onramp."
        case .deviceNotEligible:
            return "Apple Intelligence (and the on-device Foundation Model) isn’t supported on this hardware or in this region. Onramp won’t work until you use a supported Mac."
        case .other(let detail):
            return detail
        }
    }
}

#Preview("Setup") {
    FoundationModelsGateView(gate: {
        let g = FoundationModelsGateModel()
        return g
    }())
}

import AppKit
import SwiftUI

/// Compact menu-bar panel — one-click “Can't get online” playbook when allowed.
struct MenuBarQuickPanel: View {
    @EnvironmentObject private var foundationModelsGate: FoundationModelsGateModel
    @State private var isRunning = false
    @State private var summary =
        "When browsers won’t load, run the offline Can’t get online playbook."
    @State private var result: PlaybookResult?

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Onramp")
                .font(.headline)

            if foundationModelsGate.status.isHardBlock {
                Text(hardBlockSummary)
                    .font(.callout)
                    .foregroundStyle(.red)
                    .fixedSize(horizontal: false, vertical: true)
                Text("Open the main window for details. There is no workaround.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                Button("Open Onramp") { openMainWindow() }
            } else if foundationModelsGate.status.isSetupRequired,
                      !foundationModelsGate.allowPlaybooksWithoutModel
            {
                Text(setupSummary)
                    .font(.callout)
                    .foregroundStyle(.orange)
                    .fixedSize(horizontal: false, vertical: true)
                Button("Open Apple Intelligence Settings") {
                    foundationModelsGate.openSettingsAndRefresh()
                }
                .keyboardShortcut(.defaultAction)
                Button("Open Onramp") { openMainWindow() }
            } else {
                playbookBody
            }
        }
        .padding(14)
        .frame(width: 380)
    }

    private var hardBlockSummary: String {
        switch foundationModelsGate.status {
        case .unsupportedOperatingSystem:
            return "Onramp requires macOS 26+ with Apple Intelligence. This Mac’s OS isn’t supported."
        case .deviceNotEligible:
            return "This Mac isn’t eligible for Apple Intelligence — Onramp can’t run here."
        case .unavailableOther(let detail):
            return detail
        default:
            return "Onramp can’t run on this Mac."
        }
    }

    private var setupSummary: String {
        switch foundationModelsGate.status {
        case .modelNotReady:
            return "Foundation Model still downloading. Finish setup in the main window — Chat won’t work until it’s ready."
        default:
            return "Turn on Apple Intelligence (and wait for the model download) before using Onramp."
        }
    }

    @ViewBuilder
    private var playbookBody: some View {
        Text(summary)
            .font(.callout)
            .foregroundStyle(.secondary)
            .fixedSize(horizontal: false, vertical: true)
            .frame(maxWidth: .infinity, alignment: .leading)

        if let result {
            ScrollView {
                VStack(alignment: .leading, spacing: 8) {
                    Text(result.triage.headline)
                        .font(.subheadline.weight(.semibold))
                    Text(result.triage.likelyCause)
                        .font(.caption)
                    if !result.triage.actionableSteps.isEmpty {
                        Text("Next steps")
                            .font(.caption.weight(.semibold))
                        ForEach(
                            Array(result.triage.actionableSteps.prefix(3).enumerated()),
                            id: \.offset
                        ) { index, step in
                            Text("\(index + 1). \(step)")
                                .font(.caption2)
                        }
                    }
                }
                .frame(maxWidth: .infinity, alignment: .leading)
            }
            .frame(maxHeight: 220)
        }

        HStack {
            Button(isRunning ? "Running…" : "Can't get online") {
                Task { await runPlaybook() }
            }
            .disabled(isRunning)
            .keyboardShortcut(.defaultAction)
            .accessibilityIdentifier("menubar-cant-get-online")

            if let result {
                Button("Copy") {
                    PasteboardCopy.string(result.markdown)
                }
            }

            Button("Open Onramp") { openMainWindow() }
        }
    }

    private func openMainWindow() {
        NSApp.activate(ignoringOtherApps: true)
        for window in NSApp.windows where window.canBecomeMain {
            window.makeKeyAndOrderFront(nil)
            break
        }
    }

    private func runPlaybook() async {
        isRunning = true
        defer { isRunning = false }
        summary = "Gathering path, DNS, proxy, VPN, and probes…"
        result = nil
        let finished = await ConnectivityPlaybookRunner.run(kind: .cantGetOnline) { message in
            await MainActor.run {
                summary = message
            }
        }
        result = finished
        summary = finished.triage.headline
    }
}

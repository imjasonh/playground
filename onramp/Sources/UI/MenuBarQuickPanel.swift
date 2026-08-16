import AppKit
import SwiftUI

/// Compact menu-bar panel — one-click “Can't get online” playbook.
struct MenuBarQuickPanel: View {
    @State private var isRunning = false
    @State private var summary =
        "When browsers won’t load, run the offline Can’t get online playbook."
    @State private var result: PlaybookResult?

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Onramp")
                .font(.headline)

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

                Button("Open Onramp") {
                    NSApp.activate(ignoringOtherApps: true)
                    for window in NSApp.windows where window.canBecomeMain {
                        window.makeKeyAndOrderFront(nil)
                        break
                    }
                }
            }
        }
        .padding(14)
        .frame(width: 380)
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

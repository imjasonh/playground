import AppKit
import SwiftUI

/// Compact menu-bar panel for quick local checks without opening the main window first.
struct MenuBarQuickPanel: View {
    @State private var isRunning = false
    @State private var summary = "Run a quick health check for load, disk, memory pressure, and battery."
    @State private var lastReport: String?

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Geek Squad")
                .font(.headline)

            Text(summary)
                .font(.callout)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)
                .frame(maxWidth: .infinity, alignment: .leading)

            if let lastReport {
                ScrollView {
                    Text(lastReport)
                        .font(.caption.monospaced())
                        .textSelection(.enabled)
                        .frame(maxWidth: .infinity, alignment: .leading)
                }
                .frame(maxHeight: 220)
            }

            HStack {
                Button(isRunning ? "Running…" : "Quick health check") {
                    Task { await runQuickCheck() }
                }
                .disabled(isRunning)
                .keyboardShortcut(.defaultAction)

                if let lastReport {
                    Button("Copy") {
                        PasteboardCopy.string(lastReport)
                    }
                }

                Button("Open Geek Squad") {
                    NSApp.activate(ignoringOtherApps: true)
                    for window in NSApp.windows where window.canBecomeMain {
                        window.makeKeyAndOrderFront(nil)
                        break
                    }
                }
            }
        }
        .padding(14)
        .frame(width: 360)
    }

    private func runQuickCheck() async {
        isRunning = true
        defer { isRunning = false }
        summary = "Gathering load, disk, memory pressure, and battery…"
        let services = DiagnosticServices.shared
        async let load = services.systemLoad()
        async let disk = services.diskSpace()
        async let mem = services.memoryPressure()
        async let batt = services.batteryPower()
        let reports = await [load, disk, mem, batt]
        let body = reports.map { $0.compactMarkdown() }.joined(separator: "\n\n")
        lastReport = body
        summary = "Quick check finished — copy or open the main app for full triage."
    }
}

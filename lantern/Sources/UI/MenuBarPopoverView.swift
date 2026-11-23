import AppKit
import SwiftUI

/// Primary menu-bar popover: shows current network trust, live LAN/host stats,
/// active alerts with plain-English AFM explanations, and quick actions.
struct MenuBarPopoverView: View {
    @EnvironmentObject private var sentinel: SentinelController
    @EnvironmentObject private var updater: SparkleUpdater
    @Environment(\.openWindow) private var openWindow

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            headerRow
            statsStrip
            Divider()
            alertsSection
            Divider()
            footerRow
        }
        .padding(14)
        .frame(width: 400)
    }

    private var headerRow: some View {
        HStack(alignment: .center, spacing: 8) {
            Image(systemName: sentinel.safeMenuBarSymbol)
                .font(.title3)
                .foregroundStyle(statusColor)

            VStack(alignment: .leading, spacing: 2) {
                Text(sentinel.currentNetwork.displayName)
                    .font(.headline)
                    .lineLimit(1)
                HStack(spacing: 6) {
                    Text(sentinel.connectivity.statusLabel)
                        .font(.caption)
                        .foregroundStyle(sentinel.connectivity.looksHealthy ? .secondary : .orange)
                    if let last = sentinel.lastScanAt {
                        Text("· \(last, style: .relative) ago")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                }
            }

            Spacer()

            Menu {
                ForEach(NetworkTrust.allCases, id: \.self) { trust in
                    Button {
                        sentinel.setNetworkTrust(trust)
                    } label: {
                        if sentinel.currentTrust == trust {
                            Label(trust.label, systemImage: "checkmark")
                        } else {
                            Text(trust.label)
                        }
                    }
                }
            } label: {
                Text(sentinel.currentTrust.label)
                    .font(.caption.weight(.medium))
            }
            .menuStyle(.borderlessButton)
            .fixedSize()
        }
    }

    private var statsStrip: some View {
        HStack(spacing: 10) {
            statPill(
                value: "\(sentinel.devices.count)",
                label: "Devices",
                tint: .secondary
            )
            statPill(
                value: "\(sentinel.upnpMappings.count)",
                label: "UPnP",
                tint: sentinel.upnpMappings.isEmpty ? .secondary : .orange
            )
            statPill(
                value: "\(sentinel.activeFindings.count)",
                label: "Alerts",
                tint: sentinel.activeFindings.isEmpty ? .green : statusColor
            )
            Spacer()
            Button {
                Task { await sentinel.runScan(runActiveConnectivityProbes: true) }
            } label: {
                if sentinel.isScanning {
                    ProgressView()
                        .controlSize(.small)
                } else {
                    Label("Scan", systemImage: "arrow.clockwise")
                        .font(.caption.weight(.medium))
                }
            }
            .disabled(sentinel.isScanning)
        }
    }

    private func statPill(value: String, label: String, tint: Color) -> some View {
        HStack(spacing: 4) {
            Text(value)
                .font(.caption.monospacedDigit().weight(.semibold))
                .foregroundStyle(tint)
            Text(label)
                .font(.caption)
                .foregroundStyle(.secondary)
        }
        .padding(.horizontal, 8)
        .padding(.vertical, 4)
        .background(.quaternary.opacity(0.6), in: Capsule())
    }

    @ViewBuilder
    private var alertsSection: some View {
        if sentinel.activeFindings.isEmpty {
            HStack(spacing: 10) {
                Image(systemName: "checkmark.shield.fill")
                    .font(.title2)
                    .foregroundStyle(.green)
                VStack(alignment: .leading, spacing: 2) {
                    Text("All quiet on \(sentinel.currentNetwork.displayName)")
                        .font(.subheadline.weight(.medium))
                    Text("Watching devices, UPnP forwards, Mac sockets, and connectivity.")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }
            .padding(.vertical, 8)
        } else {
            ScrollView {
                VStack(alignment: .leading, spacing: 8) {
                    ForEach(sentinel.activeFindings.prefix(6)) { finding in
                        CompactPopoverFindingRow(
                            finding: finding,
                            onAcknowledge: { sentinel.acknowledge(finding: finding) },
                            onMute: { sentinel.mute(finding: finding) },
                            onInspect: { openInspector() }
                        )
                    }
                }
            }
            .frame(maxHeight: 280)
        }
    }

    private var footerRow: some View {
        HStack {
            Button("Open Inspector") {
                openInspector()
            }
            .keyboardShortcut(.defaultAction)

            if !sentinel.activeFindings.isEmpty {
                Button("Clear All") {
                    sentinel.acknowledgeAll()
                }
            }

            Spacer()

            Menu {
                Button("Check Connectivity Now") {
                    Task { await sentinel.runScan(runActiveConnectivityProbes: true) }
                }
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
                Divider()
                Button("Quit Lantern") {
                    NSApp.terminate(nil)
                }
            } label: {
                Image(systemName: "ellipsis.circle")
            }
            .menuStyle(.borderlessButton)
            .fixedSize()
        }
    }

    private var statusColor: Color {
        if !sentinel.connectivity.looksHealthy { return .orange }
        switch sentinel.highestActiveSeverity {
        case .critical: return .red
        case .warning: return .orange
        case .notice: return .blue
        case .info, .none: return .green
        }
    }

    private func openInspector() {
        openWindow(id: "inspector")
        NSApp.activate(ignoringOtherApps: true)
    }
}

private struct CompactPopoverFindingRow: View {
    let finding: Finding
    let onAcknowledge: () -> Void
    let onMute: () -> Void
    let onInspect: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack(alignment: .top, spacing: 6) {
                Image(systemName: finding.severity.symbolName)
                    .foregroundStyle(severityColor)
                    .font(.subheadline)
                VStack(alignment: .leading, spacing: 2) {
                    Text(finding.displayHeadline)
                        .font(.subheadline.weight(.semibold))
                        .fixedSize(horizontal: false, vertical: true)
                    Text(finding.displayBody)
                        .font(.caption)
                        .foregroundStyle(.secondary)
                        .fixedSize(horizontal: false, vertical: true)
                }
            }
            HStack(spacing: 8) {
                if finding.explanation?.generatedByAFM == true {
                    Label("AI", systemImage: "sparkles")
                        .font(.caption2)
                        .foregroundStyle(.secondary)
                }
                Spacer()
                Button("Dismiss", action: onAcknowledge)
                    .buttonStyle(.borderless)
                    .font(.caption)
                Button("Mute", action: onMute)
                    .buttonStyle(.borderless)
                    .font(.caption)
                Button("Inspect", action: onInspect)
                    .buttonStyle(.borderless)
                    .font(.caption.weight(.medium))
            }
        }
        .padding(10)
        .background(.quaternary.opacity(0.45), in: RoundedRectangle(cornerRadius: 8))
    }

    private var severityColor: Color {
        switch finding.severity {
        case .critical: return .red
        case .warning: return .orange
        case .notice: return .blue
        case .info: return .secondary
        }
    }
}

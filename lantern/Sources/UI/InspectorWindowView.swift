import SwiftUI

enum InspectorSection: String, CaseIterable, Identifiable {
    case alerts = "Alerts"
    case devices = "LAN Devices"
    case hostTraffic = "This Mac"
    case upnp = "UPnP Forwards"
    case connectivity = "Connectivity"
    case settings = "Settings"

    var id: String { rawValue }

    var symbolName: String {
        switch self {
        case .alerts: return "bell.badge"
        case .devices: return "network"
        case .hostTraffic: return "desktopcomputer"
        case .upnp: return "arrow.left.arrow.right.square"
        case .connectivity: return "wifi"
        case .settings: return "gearshape"
        }
    }
}

/// Full Inspector window opened on demand from the Lantern menu-bar popover.
struct InspectorWindowView: View {
    @EnvironmentObject private var sentinel: SentinelController
    @State private var selection: InspectorSection = .alerts

    var body: some View {
        NavigationSplitView {
            List(InspectorSection.allCases, selection: $selection) { section in
                HStack {
                    Label(section.rawValue, systemImage: section.symbolName)
                    Spacer()
                    if let badge = badgeCount(for: section), badge > 0 {
                        Text("\(badge)")
                            .font(.caption2.monospacedDigit().weight(.semibold))
                            .padding(.horizontal, 6)
                            .padding(.vertical, 2)
                            .background(.quaternary, in: Capsule())
                    }
                }
                .tag(section)
            }
            .navigationSplitViewColumnWidth(min: 180, ideal: 200)
        } detail: {
            Group {
                switch selection {
                case .alerts:
                    AlertsListView()
                case .devices:
                    DevicesView()
                case .hostTraffic:
                    HostTrafficView()
                case .upnp:
                    UPnPView()
                case .connectivity:
                    ConnectivityView()
                case .settings:
                    SettingsView()
                }
            }
            .toolbar {
                ToolbarItemGroup(placement: .automatic) {
                    Text(sentinel.currentNetwork.displayName)
                        .font(.callout.weight(.medium))
                        .foregroundStyle(.secondary)
                    Button {
                        Task { await sentinel.runScan(runActiveConnectivityProbes: true) }
                    } label: {
                        Label("Scan Now", systemImage: "arrow.clockwise")
                    }
                    .disabled(sentinel.isScanning)
                }
            }
        }
    }

    private func badgeCount(for section: InspectorSection) -> Int? {
        switch section {
        case .alerts: return sentinel.activeFindings.count
        case .devices: return sentinel.devices.count
        case .upnp: return sentinel.upnpMappings.count
        default: return nil
        }
    }
}

private struct AlertsListView: View {
    @EnvironmentObject private var sentinel: SentinelController
    @State private var showDismissed = false

    private var displayedFindings: [Finding] {
        showDismissed ? sentinel.findings : sentinel.activeFindings
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                Text("Alerts")
                    .font(.title2.weight(.semibold))
                Spacer()
                Toggle("Show dismissed", isOn: $showDismissed)
                    .toggleStyle(.checkbox)
                if !sentinel.activeFindings.isEmpty {
                    Button("Dismiss All") { sentinel.acknowledgeAll() }
                }
            }
            .padding()

            Divider()

            if displayedFindings.isEmpty {
                ContentUnavailableView(
                    "No Active Alerts",
                    systemImage: "checkmark.shield",
                    description: Text("Lantern is watching \(sentinel.currentNetwork.displayName) in the background.")
                )
            } else {
                ScrollView {
                    LazyVStack(alignment: .leading, spacing: 10) {
                        ForEach(displayedFindings) { finding in
                            let device = finding.subjectID.flatMap { id in
                                sentinel.devices.first { $0.id == id || $0.ipAddress == id }
                            }
                            FindingCardView(
                                finding: finding,
                                relatedDevice: device,
                                onAcknowledge: { sentinel.acknowledge(finding: finding) },
                                onMute: { sentinel.mute(finding: finding) },
                                onTrustSubject: trustClosure(for: finding, device: device)
                            )
                        }
                    }
                    .padding()
                }
            }
        }
    }

    private func trustClosure(for finding: Finding, device: LANDevice?) -> (() -> Void)? {
        if let device, !device.isTrusted {
            return { sentinel.trust(device: device, trusted: true) }
        }
        if (finding.kind == .hostProcessHighFanOut || finding.kind == .hostProcessWildcardListener),
           let proc = finding.subjectID
        {
            return { sentinel.trustProcess(proc) }
        }
        return nil
    }
}

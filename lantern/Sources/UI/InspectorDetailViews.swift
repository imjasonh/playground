import SwiftUI

// MARK: - LAN Devices

struct DevicesView: View {
    @EnvironmentObject private var sentinel: SentinelController
    @State private var selectedDevice: LANDevice?

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("LAN Devices (\(sentinel.devices.count))")
                        .font(.title2.weight(.semibold))
                    Text("Passively observed via ARP and mDNS. Click Explore on any device to run active probes.")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
                Spacer()
                Text("Network: \(sentinel.currentNetwork.displayName)")
                    .font(.callout)
                    .foregroundStyle(.secondary)
            }
            .padding()

            Divider()

            if sentinel.devices.isEmpty {
                ContentUnavailableView(
                    "No Devices Observed Yet",
                    systemImage: "network",
                    description: Text("Lantern listens passively for devices on your local network.")
                )
            } else {
                List(sentinel.devices) { device in
                    HStack(alignment: .top, spacing: 12) {
                        Image(systemName: icon(for: device))
                            .font(.title3)
                            .frame(width: 24)
                            .foregroundStyle(device.suspiciousPorts.isEmpty ? Color.secondary : Color.orange)

                        VStack(alignment: .leading, spacing: 3) {
                            HStack(spacing: 6) {
                                Text(device.displayName)
                                    .font(.headline)
                                if device.isGateway {
                                    pill("Gateway", tint: .blue)
                                }
                                if device.isThisMac {
                                    pill("This Mac", tint: .green)
                                }
                                if let cat = device.classification?.category, cat != "Unknown" {
                                    pill(cat, tint: .secondary)
                                }
                            }

                            Text("\(device.ipAddress) · \(device.macAddress)\(device.vendor.map { " · \($0)" } ?? "")")
                                .font(.caption.monospaced())
                                .foregroundStyle(.secondary)

                            if !device.openPorts.isEmpty {
                                let portList = device.openPorts
                                    .map { "\($0.port)/\($0.serviceName)" }
                                    .joined(separator: ", ")
                                Text("Open ports: \(portList)")
                                    .font(.caption)
                                    .foregroundStyle(device.suspiciousPorts.isEmpty ? Color.secondary : Color.orange)
                            }

                            if let note = device.classification?.riskNote {
                                Text(note)
                                    .font(.caption)
                                    .foregroundStyle(.orange)
                            }
                        }

                        Spacer()

                        HStack(spacing: 10) {
                            Button("Explore…") {
                                selectedDevice = device
                            }
                            .controlSize(.small)

                            Toggle(
                                "Trusted",
                                isOn: Binding(
                                    get: { device.isTrusted },
                                    set: { sentinel.trust(device: device, trusted: $0) }
                                )
                            )
                            .toggleStyle(.checkbox)
                        }
                    }
                    .padding(.vertical, 4)
                }
            }
        }
        .sheet(item: $selectedDevice) { device in
            DeviceExplorerSheet(device: device)
                .environmentObject(sentinel)
        }
    }

    private func icon(for device: LANDevice) -> String {
        if device.isGateway { return "wifi.router" }
        if device.isThisMac { return "laptopcomputer" }
        switch device.classification?.category.lowercased() {
        case "printer": return "printer"
        case "tv": return "appletv"
        case "speaker": return "hifispeaker"
        case "camera": return "video"
        case "server": return "server.rack"
        default: return "network"
        }
    }

    private func pill(_ text: String, tint: Color) -> some View {
        Text(text)
            .font(.caption2.weight(.semibold))
            .padding(.horizontal, 6)
            .padding(.vertical, 2)
            .background(tint.opacity(0.15), in: Capsule())
            .foregroundStyle(tint)
    }
}

// MARK: - This Mac (Process Fan-Out & Listeners)

struct HostTrafficView: View {
    @EnvironmentObject private var sentinel: SentinelController

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("This Mac's Network Processes")
                        .font(.title2.weight(.semibold))
                    Text("Sorted by external /16 subnet diversity to spot residential-proxy SDKs and chatty apps.")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
                Spacer()
            }
            .padding()

            Divider()

            if sentinel.hostProcesses.isEmpty {
                ContentUnavailableView(
                    "No Active Socket Snapshots",
                    systemImage: "desktopcomputer",
                    description: Text("Run a scan to inspect this Mac's outbound fan-out and listening ports.")
                )
            } else {
                List(sentinel.hostProcesses) { proc in
                    HStack(alignment: .top) {
                        VStack(alignment: .leading, spacing: 3) {
                            HStack(spacing: 6) {
                                Text(proc.processName)
                                    .font(.headline)
                                Text("PID \(proc.pid)")
                                    .font(.caption.monospaced())
                                    .foregroundStyle(.secondary)
                            }
                            Text("\(proc.uniqueRemoteIPs) remote IPs across \(proc.uniqueRemoteSubnets) /16 subnets · \(proc.establishedConnections) established")
                                .font(.caption)
                                .foregroundStyle(.secondary)
                            if !proc.listeningWildcardPorts.isEmpty {
                                let ports = proc.listeningWildcardPorts.map { ":\($0)" }.joined(separator: ", ")
                                Text("Listening on LAN: \(ports)")
                                    .font(.caption.monospaced())
                                    .foregroundStyle(.orange)
                            }
                        }

                        Spacer()

                        VStack(alignment: .trailing, spacing: 2) {
                            Text("↑ \(formatBytes(proc.bytesOut))  ↓ \(formatBytes(proc.bytesIn))")
                                .font(.caption.monospacedDigit())
                            if proc.bytesOut + proc.bytesIn > 0 {
                                Text("\(Int((proc.uploadRatio * 100).rounded()))% upload")
                                    .font(.caption2)
                                    .foregroundStyle(proc.uploadRatio >= 0.65 ? Color.orange : Color.secondary)
                            }
                        }
                    }
                    .padding(.vertical, 3)
                }
            }
        }
    }

    private func formatBytes(_ bytes: UInt64) -> String {
        ByteCountFormatter.string(fromByteCount: Int64(clamping: bytes), countStyle: .file)
    }
}

// MARK: - UPnP Forwards

struct UPnPView: View {
    @EnvironmentObject private var sentinel: SentinelController

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("Router UPnP Port Forwards")
                        .font(.title2.weight(.semibold))
                    Text("Inbound ports punched through your router by devices on the LAN.")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
                Spacer()
            }
            .padding()

            Divider()

            if sentinel.upnpMappings.isEmpty {
                ContentUnavailableView(
                    "No Active UPnP Forwards",
                    systemImage: "checkmark.shield",
                    description: Text("Either UPnP is disabled on your router (good!) or no devices have requested port forwards.")
                )
            } else {
                List(sentinel.upnpMappings) { mapping in
                    HStack {
                        VStack(alignment: .leading, spacing: 3) {
                            Text("\(mapping.protocolName) :\(mapping.externalPort) → \(mapping.internalClient):\(mapping.internalPort)")
                                .font(.headline.monospaced())
                            Text(mapping.description.isEmpty ? "No description" : mapping.description)
                                .font(.caption)
                                .foregroundStyle(.secondary)
                        }
                        Spacer()
                        Text(mapping.leaseDuration == 0 ? "Permanent" : "\(mapping.leaseDuration)s lease")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                    .padding(.vertical, 3)
                }
            }
        }
    }
}

// MARK: - Connectivity

struct ConnectivityView: View {
    @EnvironmentObject private var sentinel: SentinelController

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 16) {
                HStack {
                    VStack(alignment: .leading, spacing: 2) {
                        Text("Connectivity & Local Config")
                            .font(.title2.weight(.semibold))
                        Text("Path, gateway, DNS, VPN, system proxies, and /etc/hosts.")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                    Spacer()
                    Button("Run Active Probes") {
                        Task { await sentinel.runScan(runActiveConnectivityProbes: true) }
                    }
                    .disabled(sentinel.isScanning)
                }

                let conn = sentinel.connectivity
                GroupBox("Current State") {
                    Grid(alignment: .leading, horizontalSpacing: 16, verticalSpacing: 8) {
                        row("Status", conn.statusLabel)
                        row("Interface", conn.defaultInterface ?? "None")
                        row("Gateway", conn.defaultGateway ?? "None")
                        row("DNS Servers", conn.dnsServers.isEmpty ? "None" : conn.dnsServers.joined(separator: ", "))
                        row("VPN Active", conn.isVPNActive ? "Yes (\(conn.vpnInterfaces.joined(separator: ", ")))" : "No")
                        row("System Proxy", conn.proxySummary ?? "Disabled")
                        row("DNS Lookup Probe", probeLabel(conn.dnsResolves))
                        row("HTTP / Captive Probe", conn.captivePortalSuspected ? "Captive portal detected" : probeLabel(conn.httpProbeOK))
                    }
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(6)
                }

                if !conn.suspiciousHostsEntries.isEmpty {
                    GroupBox("Custom /etc/hosts Overrides") {
                        VStack(alignment: .leading, spacing: 4) {
                            ForEach(conn.suspiciousHostsEntries, id: \.self) { line in
                                Text(line)
                                    .font(.caption.monospaced())
                            }
                        }
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(6)
                    }
                }
            }
            .padding()
        }
    }

    private func row(_ label: String, _ value: String) -> some View {
        GridRow {
            Text(label)
                .font(.callout.weight(.medium))
                .foregroundStyle(.secondary)
            Text(value)
                .font(.callout.monospaced())
                .textSelection(.enabled)
        }
    }

    private func probeLabel(_ value: Bool?) -> String {
        switch value {
        case .some(true): return "OK"
        case .some(false): return "Failed"
        case .none: return "Not run yet"
        }
    }
}

// MARK: - Settings & External Vantage

struct SettingsView: View {
    @EnvironmentObject private var sentinel: SentinelController

    var body: some View {
        Form {
            Section("Monitoring") {
                Stepper(
                    "Scan interval: \(sentinel.scanIntervalSeconds)s",
                    value: $sentinel.scanIntervalSeconds,
                    in: 15...600,
                    step: 15
                )
                Toggle("macOS Notifications (Trusted LANs only)", isOn: $sentinel.notificationsEnabled)
            }

            Section("Apple Intelligence (Optional)") {
                LabeledContent("Status", value: sentinel.afmAvailability.shortLabel)
                if !sentinel.afmAvailability.isAvailable {
                    Button("Open Apple Intelligence Settings") {
                        AppleIntelligenceSettings.open()
                    }
                }
            }

            Section("External DNS Vantage Point (Optional)") {
                Picker("Provider", selection: $sentinel.externalVantageConfig.provider) {
                    ForEach(ExternalVantageConfig.Provider.allCases, id: \.self) { provider in
                        Text(provider.label).tag(provider)
                    }
                }
                if sentinel.externalVantageConfig.provider != .none {
                    TextField("Base URL (e.g. http://192.168.1.2)", text: $sentinel.externalVantageConfig.baseURL)
                    SecureField("API Token or user:password", text: $sentinel.externalVantageConfig.apiToken)
                    Stepper(
                        "Chatty client threshold: \(sentinel.externalVantageConfig.chattyQueryThreshold) queries",
                        value: $sentinel.externalVantageConfig.chattyQueryThreshold,
                        in: 500...50_000,
                        step: 500
                    )
                }
                if let ext = sentinel.externalVantage {
                    if let err = ext.errorMessage {
                        Text("Last error: \(err)")
                            .font(.caption)
                            .foregroundStyle(.orange)
                    } else {
                        Text("Connected to \(ext.sourceName): \(ext.chattyClients.count) clients reported.")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                }
            }

            Section {
                Button("Save Settings") {
                    sentinel.saveSettings()
                }
                .keyboardShortcut(.defaultAction)
            }

            if !sentinel.muteRules.isEmpty {
                Section("Muted Rules (\(sentinel.muteRules.count))") {
                    ForEach(sentinel.muteRules) { rule in
                        HStack {
                            VStack(alignment: .leading) {
                                Text(rule.label)
                                    .font(.callout)
                                Text(rule.dedupeKey)
                                    .font(.caption2.monospaced())
                                    .foregroundStyle(.secondary)
                            }
                            Spacer()
                            Button("Unmute") {
                                sentinel.removeMuteRule(id: rule.id)
                            }
                        }
                    }
                }
            }
        }
        .formStyle(.grouped)
        .padding()
    }
}

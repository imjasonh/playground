import AppKit
import SwiftUI

/// Interactive per-device explorer sheet.
/// Background scans stay strictly passive; every probe here only sends traffic after an explicit click.
struct DeviceExplorerSheet: View {
    let device: LANDevice
    @EnvironmentObject private var sentinel: SentinelController
    @Environment(\.dismiss) private var dismiss

    @State private var isProbing = false
    @State private var openPorts: [OpenPort]
    @State private var pingResult: DeviceExplorer.PingResult?
    @State private var httpResults: [DeviceExplorer.HTTPFingerprint] = []
    @State private var bannerResults: [DeviceExplorer.BannerResult] = []
    @State private var customPortText = "8080"
    @State private var statusMessage: String?

    init(device: LANDevice) {
        self.device = device
        _openPorts = State(initialValue: device.openPorts)
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 14) {
            header
            Divider()
            actionBar
            if let statusMessage {
                Text(statusMessage)
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
            ScrollView {
                VStack(alignment: .leading, spacing: 12) {
                    identityBox
                    portsBox
                    if let pingResult {
                        pingBox(pingResult)
                    }
                    if !httpResults.isEmpty {
                        httpBox
                    }
                    if !bannerResults.isEmpty {
                        bannerBox
                    }
                }
            }
        }
        .padding(18)
        .frame(width: 620, height: 520)
    }

    private var header: some View {
        HStack(alignment: .top) {
            VStack(alignment: .leading, spacing: 3) {
                Text(device.displayName)
                    .font(.title2.weight(.semibold))
                Text("\(device.ipAddress) · \(device.macAddress)\(device.vendor.map { " · \($0)" } ?? "")")
                    .font(.caption.monospaced())
                    .foregroundStyle(.secondary)
            }
            Spacer()
            if isProbing {
                ProgressView().controlSize(.small)
            }
            Button("Done") { dismiss() }
        }
    }

    private var actionBar: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Active Probes (sent only when clicked)")
                .font(.caption.weight(.semibold))
                .foregroundStyle(.secondary)

            HStack(spacing: 8) {
                Button("Probe Ports") { Task { await runPortProbe() } }
                Button("Ping (4×)") { Task { await runPing() } }
                Button("HTTP / TLS") { Task { await runHTTPInspect() } }
                Button("SOCKS Proxy Test") { Task { await runBanner(port: 1080) } }
                Button("Re-classify (AI)") { Task { await reclassify() } }
                Spacer()
                Button("Open HTTP") {
                    if let url = URL(string: "http://\(device.ipAddress)") {
                        NSWorkspace.shared.open(url)
                    }
                }
            }
            .disabled(isProbing)
            .controlSize(.small)

            HStack(spacing: 8) {
                Text("Custom TCP banner:")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                TextField("Port", text: $customPortText)
                    .textFieldStyle(.roundedBorder)
                    .frame(width: 80)
                Button("Grab Banner") {
                    if let port = UInt16(customPortText.trimmingCharacters(in: .whitespaces)) {
                        Task { await runBanner(port: port) }
                    }
                }
                .disabled(isProbing)
                .controlSize(.small)

                Spacer()

                Button("Wake-on-LAN") {
                    let ok = DeviceExplorer.sendWakeOnLAN(mac: device.macAddress)
                    statusMessage = ok
                        ? "Sent Wake-on-LAN magic packet to \(device.macAddress)."
                        : "Could not send Wake-on-LAN packet."
                }
                .controlSize(.small)
            }
        }
    }

    private var identityBox: some View {
        GroupBox("Observed Identity (Passive)") {
            VStack(alignment: .leading, spacing: 4) {
                if let host = device.hostname {
                    Text("Hostname: \(host)").font(.caption.monospaced())
                }
                if let cls = device.classification {
                    Text("Classification: \(cls.friendlyName) [\(cls.category)] (\(cls.source == .foundationModel ? "Apple Intelligence" : "Heuristic"))")
                        .font(.caption)
                    if let risk = cls.riskNote {
                        Text("Note: \(risk)")
                            .font(.caption)
                            .foregroundStyle(.orange)
                    }
                }
                if !device.mdnsServices.isEmpty {
                    Text("mDNS Services: \(device.mdnsServices.joined(separator: ", "))")
                        .font(.caption.monospaced())
                        .foregroundStyle(.secondary)
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(4)
        }
    }

    private var portsBox: some View {
        GroupBox("Open Ports (\(openPorts.count))") {
            if openPorts.isEmpty {
                Text("No open ports recorded yet. Click 'Probe Ports' to scan high-signal TCP ports on this device.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(4)
            } else {
                VStack(alignment: .leading, spacing: 6) {
                    ForEach(openPorts) { port in
                        HStack {
                            Text("\(port.port)/tcp — \(port.serviceName)")
                                .font(.caption.monospaced())
                                .foregroundStyle(port.isSuspicious ? Color.orange : Color.primary)
                            Spacer()
                            Button("Banner") {
                                Task { await runBanner(port: port.port) }
                            }
                            .controlSize(.mini)
                        }
                    }
                }
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(4)
            }
        }
    }

    private func pingBox(_ ping: DeviceExplorer.PingResult) -> some View {
        GroupBox("ICMP Ping") {
            Text(ping.rawSummary)
                .font(.caption.monospaced())
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding(4)
        }
    }

    private var httpBox: some View {
        GroupBox("HTTP / HTTPS Inspection") {
            VStack(alignment: .leading, spacing: 8) {
                ForEach(httpResults, id: \.url) { item in
                    VStack(alignment: .leading, spacing: 2) {
                        Text(item.url)
                            .font(.caption.monospaced().weight(.semibold))
                        if let code = item.statusCode {
                            Text("Status: HTTP \(code)")
                                .font(.caption.monospaced())
                        }
                        if let title = item.pageTitle {
                            Text("Title: \(title)")
                                .font(.caption)
                        }
                        if let server = item.serverHeader {
                            Text("Server: \(server)")
                                .font(.caption.monospaced())
                                .foregroundStyle(.secondary)
                        }
                        if let cert = item.tlsCertSubject {
                            Text("TLS Cert Subject: \(cert)")
                                .font(.caption.monospaced())
                                .foregroundStyle(.secondary)
                        }
                        if let err = item.errorMessage {
                            Text("Error: \(err)")
                                .font(.caption)
                                .foregroundStyle(.secondary)
                        }
                    }
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(4)
        }
    }

    private var bannerBox: some View {
        GroupBox("TCP Banner & Proxy Tests") {
            VStack(alignment: .leading, spacing: 8) {
                ForEach(bannerResults, id: \.port) { res in
                    VStack(alignment: .leading, spacing: 2) {
                        Text("Port \(res.port): \(res.note)")
                            .font(.caption.weight(.semibold))
                            .foregroundStyle(res.looksLikeOpenProxy ? Color.red : Color.primary)
                        if let banner = res.banner {
                            Text(banner)
                                .font(.caption.monospaced())
                                .foregroundStyle(.secondary)
                                .textSelection(.enabled)
                        }
                    }
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(4)
        }
    }

    // MARK: - Probe runners

    private func runPortProbe() async {
        isProbing = true
        statusMessage = "Probing \(DeviceExplorer.interactivePortSpecs.count) TCP ports on \(device.ipAddress)…"
        defer { isProbing = false }
        let found = await PortProbeCollector.probeHost(
            ip: device.ipAddress,
            specs: DeviceExplorer.interactivePortSpecs
        )
        openPorts = found
        sentinel.recordInteractivePortProbe(deviceID: device.id, openPorts: found)
        statusMessage = "Found \(found.count) open port(s) on \(device.ipAddress)."
    }

    private func runPing() async {
        isProbing = true
        statusMessage = "Pinging \(device.ipAddress)…"
        defer { isProbing = false }
        let res = await DeviceExplorer.ping(ip: device.ipAddress)
        pingResult = res
        statusMessage = res.rawSummary
    }

    private func runHTTPInspect() async {
        isProbing = true
        statusMessage = "Inspecting HTTP & HTTPS headers on \(device.ipAddress)…"
        defer { isProbing = false }
        async let http80 = DeviceExplorer.inspectHTTP(ip: device.ipAddress, port: 80, useHTTPS: false)
        async let https443 = DeviceExplorer.inspectHTTP(ip: device.ipAddress, port: 443, useHTTPS: true)
        var results = [await http80, await https443]
        if openPorts.contains(where: { $0.port == 8080 }) {
            results.append(await DeviceExplorer.inspectHTTP(ip: device.ipAddress, port: 8080, useHTTPS: false))
        }
        httpResults = results
        statusMessage = "HTTP/TLS inspection complete."
    }

    private func runBanner(port: UInt16) async {
        isProbing = true
        statusMessage = "Connecting to \(device.ipAddress):\(port)…"
        defer { isProbing = false }
        let res = await DeviceExplorer.grabBanner(ip: device.ipAddress, port: port)
        bannerResults.removeAll { $0.port == port }
        bannerResults.insert(res, at: 0)
        statusMessage = res.note
    }

    private func reclassify() async {
        isProbing = true
        statusMessage = "Classifying device with latest probe facts…"
        defer { isProbing = false }
        var enriched = device
        enriched.openPorts = openPorts
        let classification = await DeviceClassifier.classify(enriched)
        sentinel.updateDeviceClassification(deviceID: device.id, classification: classification)
        statusMessage = "Classified as: \(classification.friendlyName) [\(classification.category)]."
    }
}

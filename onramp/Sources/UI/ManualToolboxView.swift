import AppKit
import SwiftUI

struct ManualToolboxView: View {
    @State private var selection: ToolboxCheck? = .pathStatus
    @State private var hostField = ToolboxCheck.pathStatus.defaultHost
    @State private var portField = "443"
    @State private var isRunning = false
    @State private var report: DiagnosticReport?
    @State private var errorText: String?

    private let services = DiagnosticServices.shared

    var body: some View {
        NavigationSplitView {
            List(selection: $selection) {
                Section("Network (offline triage)") {
                    ForEach(ToolboxCheck.networkCases) { check in
                        checkRow(check)
                    }
                }
                Section("Advanced (once you're online)") {
                    ForEach(ToolboxCheck.advancedCases) { check in
                        checkRow(check)
                    }
                }
            }
            .navigationSplitViewColumnWidth(min: 200, ideal: 240)
            .navigationTitle("Toolbox")
        } detail: {
            detailPane
        }
    }

    private func checkRow(_ check: ToolboxCheck) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(check.title)
            Text(check.subtitle)
                .font(.caption)
                .foregroundStyle(.secondary)
        }
        .tag(check)
        .accessibilityIdentifier("check-\(check.rawValue)")
    }

    @ViewBuilder
    private var detailPane: some View {
        if let selection {
            VStack(alignment: .leading, spacing: 16) {
                Text(selection.title)
                    .font(.title2.weight(.semibold))
                Text(selection.subtitle)
                    .foregroundStyle(.secondary)

                if !selection.isNetwork {
                    Text(
                        "These checks are secondary — once you can get online, search engines usually beat a local tool. Prefer Playbooks when browsers won’t load."
                    )
                    .font(.callout)
                    .foregroundStyle(.orange)
                }

                if selection.needsHostField {
                    HStack {
                        TextField(selection.hostPlaceholder, text: $hostField)
                            .textFieldStyle(.roundedBorder)
                            .accessibilityIdentifier("host-field")
                        if selection == .reachability {
                            TextField("port", text: $portField)
                                .frame(width: 72)
                                .textFieldStyle(.roundedBorder)
                                .accessibilityIdentifier("port-field")
                        }
                    }
                }

                HStack {
                    Button(isRunning ? "Running…" : "Run check") {
                        Task { await run(selection) }
                    }
                    .disabled(isRunning)
                    .keyboardShortcut(.defaultAction)
                    .accessibilityIdentifier("run-check")

                    if let report, !report.body.isEmpty {
                        Button("Copy report") {
                            copyToPasteboard(report.markdown)
                        }
                        .accessibilityIdentifier("copy-report")
                    }
                }

                if let errorText {
                    Text(errorText)
                        .foregroundStyle(.red)
                }

                if let report {
                    DiagnosticResultView(report: report)
                } else if !isRunning {
                    Text(
                        "Single checks for drilling in after a playbook. Fixes are proposed only — nothing is changed on your Mac."
                    )
                    .foregroundStyle(.secondary)
                }

                Spacer(minLength: 0)
            }
            .padding(20)
            .onChange(of: self.selection) { _, newValue in
                report = nil
                errorText = nil
                if let newValue, newValue.needsHostField {
                    hostField = newValue.defaultHost
                }
            }
        } else {
            ContentUnavailableView(
                "Select a check",
                systemImage: "wrench.and.screwdriver",
                description: Text("Choose a toolbox check from the list to run it.")
            )
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func run(_ check: ToolboxCheck) async {
        isRunning = true
        errorText = nil
        report = nil
        defer { isRunning = false }
        let port = UInt16(portField) ?? 443
        switch check {
        case .interfaces: report = await services.interfaces()
        case .defaultRoute: report = await services.defaultRoute()
        case .pathStatus: report = await services.pathStatus()
        case .dnsConfig: report = await services.dnsConfig()
        case .dnsLookup: report = await services.dnsLookup(hostname: hostField)
        case .dnsTrace: report = await services.dnsTrace(hostname: hostField)
        case .reachability: report = await services.reachability(host: hostField, port: port)
        case .ping: report = await services.ping(host: hostField)
        case .traceroute: report = await services.traceroute(host: hostField)
        case .httpProbe: report = await services.httpProbe(urlString: hostField)
        case .proxyConfig: report = await services.proxyConfig()
        case .vpnInterfaces: report = await services.vpnInterfaces()
        case .hostsFile: report = await services.hostsFile()
        case .currentWifi: report = await services.currentWifi()
        case .arpNeighbors: report = await services.arpNeighbors()
        case .processUsage: report = await services.processUsage(query: hostField)
        case .topMemory: report = await services.topMemoryProcesses()
        case .topCPU: report = await services.topCPUProcesses()
        case .diskSpace: report = await services.diskSpace()
        case .memoryPressure: report = await services.memoryPressure()
        case .systemLoad: report = await services.systemLoad()
        case .powerAssertions: report = await services.powerAssertions()
        case .listeningPorts:
            let trimmed = hostField.trimmingCharacters(in: .whitespacesAndNewlines)
            report = await services.listeningPorts(port: Int(trimmed))
        case .crashReports:
            let trimmed = hostField.trimmingCharacters(in: .whitespacesAndNewlines)
            report = await services.recentCrashReports(query: trimmed.isEmpty ? nil : trimmed)
        case .loginItems: report = await services.loginItems()
        case .userStorage: report = await services.userStorageHotspots()
        case .batteryPower: report = await services.batteryPower()
        }
    }

    private func copyToPasteboard(_ string: String) {
        PasteboardCopy.string(string)
    }
}

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
            List(ToolboxCheck.allCases, selection: $selection) { check in
                VStack(alignment: .leading, spacing: 2) {
                    Text(check.title)
                    Text(check.subtitle)
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
                .tag(check)
                .accessibilityIdentifier("check-\(check.rawValue)")
            }
            .navigationSplitViewColumnWidth(min: 200, ideal: 240)
            .navigationTitle("Toolbox")
        } detail: {
            detailPane
        }
    }

    @ViewBuilder
    private var detailPane: some View {
        if let selection {
            VStack(alignment: .leading, spacing: 16) {
                Text(selection.title)
                    .font(.title2.weight(.semibold))
                Text(selection.subtitle)
                    .foregroundStyle(.secondary)

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
                    Text("Run a check to see results. Fixes are proposed only — nothing is changed on your Mac.")
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
            Text("Select a check")
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func run(_ check: ToolboxCheck) async {
        isRunning = true
        errorText = nil
        defer { isRunning = false }
        let result: DiagnosticReport
        switch check {
        case .interfaces:
            result = await services.interfaces()
        case .defaultRoute:
            result = await services.defaultRoute()
        case .pathStatus:
            result = await services.pathStatus()
        case .dnsConfig:
            result = await services.dnsConfig()
        case .dnsLookup:
            result = await services.dnsLookup(hostname: hostField)
        case .reachability:
            let port = UInt16(portField) ?? 443
            result = await services.reachability(host: hostField, port: port)
        case .httpProbe:
            result = await services.httpProbe(urlString: hostField)
        case .proxyConfig:
            result = await services.proxyConfig()
        case .vpnInterfaces:
            result = await services.vpnInterfaces()
        case .hostsFile:
            result = await services.hostsFile()
        case .currentWifi:
            result = await services.currentWifi()
        case .processUsage:
            result = await services.processUsage(query: hostField)
        case .topMemory:
            result = await services.topMemoryProcesses()
        }
        report = result
    }

    private func copyToPasteboard(_ text: String) {
        #if os(macOS)
        let pb = NSPasteboard.general
        pb.clearContents()
        pb.setString(text, forType: .string)
        #endif
    }
}

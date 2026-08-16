import SwiftUI

/// Primary surface: offline playbooks that chain network checks and rank causes.
struct PlaybooksView: View {
    @State private var selection: ConnectivityPlaybookKind? = .cantGetOnline
    @State private var isRunning = false
    @State private var progress = ""
    @State private var result: PlaybookResult?
    @State private var showRawChecks = false

    var body: some View {
        NavigationSplitView {
            List(ConnectivityPlaybookKind.allCases, selection: $selection) { kind in
                Label {
                    VStack(alignment: .leading, spacing: 2) {
                        Text(kind.title)
                        Text(kind.subtitle)
                            .font(.caption)
                            .foregroundStyle(.secondary)
                            .fixedSize(horizontal: false, vertical: true)
                    }
                } icon: {
                    Image(systemName: kind.symbolName)
                }
                .tag(kind)
                .accessibilityIdentifier("playbook-\(kind.rawValue)")
            }
            .navigationSplitViewColumnWidth(min: 240, ideal: 280)
            .navigationTitle("Playbooks")
        } detail: {
            detailPane
        }
    }

    @ViewBuilder
    private var detailPane: some View {
        if let selection {
            ScrollView {
                VStack(alignment: .leading, spacing: 16) {
                    HStack(alignment: .top, spacing: 12) {
                        Image(systemName: selection.symbolName)
                            .font(.largeTitle)
                            .foregroundStyle(.tint)
                            .accessibilityHidden(true)
                        VStack(alignment: .leading, spacing: 4) {
                            Text(selection.title)
                                .font(.title2.weight(.semibold))
                            Text(selection.subtitle)
                                .foregroundStyle(.secondary)
                        }
                    }

                    if selection == .cantGetOnline {
                        Text(
                            "Best starting point when browsers won’t load. Runs path, route, DNS, proxy, VPN, hosts, then live probes — works fully offline for local config, and uses the network only for the probes themselves."
                        )
                        .foregroundStyle(.secondary)
                    }

                    HStack {
                        Button(isRunning ? "Running…" : "Run playbook") {
                            Task { await run(selection) }
                        }
                        .disabled(isRunning)
                        .keyboardShortcut(.defaultAction)
                        .accessibilityIdentifier("run-playbook")

                        if let result {
                            Button("Copy report") {
                                PasteboardCopy.string(result.markdown)
                            }
                            .accessibilityIdentifier("copy-playbook-report")
                        }
                    }

                    if isRunning {
                        HStack(spacing: 8) {
                            ProgressView()
                                .controlSize(.small)
                            Text(progress.isEmpty ? "Working…" : progress)
                                .foregroundStyle(.secondary)
                        }
                        .accessibilityIdentifier("playbook-progress")
                    }

                    if let result {
                        TriageReportCard(report: result.triage)

                        DisclosureGroup("Raw checks (\(result.checks.count))", isExpanded: $showRawChecks) {
                            VStack(alignment: .leading, spacing: 12) {
                                ForEach(Array(result.checks.enumerated()), id: \.offset) { _, check in
                                    VStack(alignment: .leading, spacing: 6) {
                                        Text(check.title)
                                            .font(.headline)
                                        Text(check.body)
                                            .font(.caption.monospaced())
                                            .textSelection(.enabled)
                                    }
                                    .padding(10)
                                    .frame(maxWidth: .infinity, alignment: .leading)
                                    .background(Color.primary.opacity(0.04))
                                    .clipShape(RoundedRectangle(cornerRadius: 8))
                                }
                            }
                            .padding(.top, 8)
                        }
                        .accessibilityIdentifier("playbook-raw-checks")
                    } else if !isRunning {
                        Text(
                            "Run to get a ranked likely cause plus proposed steps. Nothing is changed on your Mac — fixes are for you to apply."
                        )
                        .foregroundStyle(.secondary)
                    }

                    Spacer(minLength: 0)
                }
                .padding(20)
            }
            .onChange(of: self.selection) { _, _ in
                result = nil
                progress = ""
                showRawChecks = false
            }
        } else {
            Text("Select a playbook")
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func run(_ kind: ConnectivityPlaybookKind) async {
        isRunning = true
        progress = "Starting…"
        result = nil
        defer { isRunning = false }
        let finished = await ConnectivityPlaybookRunner.run(kind: kind) { message in
            await MainActor.run {
                progress = message
            }
        }
        result = finished
        progress = "Done"
    }
}

#Preview {
    PlaybooksView()
}

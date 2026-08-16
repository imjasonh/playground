import SwiftUI

/// Primary surface: offline playbooks that chain network checks and rank causes.
struct PlaybooksView: View {
    @EnvironmentObject private var foundationModelsGate: FoundationModelsGateModel
    @EnvironmentObject private var onboarding: OnboardingModel
    /// When true (default for golden path), auto-run Can’t get online on appear.
    var autoStartCantGetOnline: Bool = true

    @State private var selection: ConnectivityPlaybookKind? = .cantGetOnline
    @State private var isRunning = false
    @State private var progress = ""
    @State private var result: PlaybookResult?
    @State private var showRawChecks = false
    @State private var actionLog: [String] = []
    @State private var didAutoStart = false

    var body: some View {
        VStack(spacing: 0) {
            if foundationModelsGate.allowPlaybooksWithoutModel,
               foundationModelsGate.status.isSetupRequired
            {
                modelSetupNudge
            }
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
        .task {
            await maybeAutoStart()
        }
    }

    private var modelSetupNudge: some View {
        HStack(alignment: .top, spacing: 12) {
            Image(systemName: "exclamationmark.triangle.fill")
                .foregroundStyle(.orange)
            VStack(alignment: .leading, spacing: 4) {
                Text("Finish Apple Intelligence setup")
                    .font(.headline)
                Text(
                    foundationModelsGate.status == .modelNotReady
                        ? "The on-device model is still downloading. Playbooks work; Chat won’t until it finishes."
                        : "Enable Apple Intelligence and download the on-device model — Chat needs it."
                )
                .font(.callout)
                .foregroundStyle(.secondary)
            }
            Spacer(minLength: 8)
            Button("Set up…") {
                foundationModelsGate.allowPlaybooksWithoutModel = false
                foundationModelsGate.refresh()
            }
            .buttonStyle(.borderedProminent)
            .controlSize(.small)
            .accessibilityIdentifier("playbooks-finish-setup")
        }
        .padding(12)
        .background(Color.orange.opacity(0.12))
        .accessibilityIdentifier("playbooks-model-nudge")
    }

    @ViewBuilder
    private var detailPane: some View {
        if let selection {
            ScrollView {
                VStack(alignment: .leading, spacing: 16) {
                    header(for: selection)

                    if selection == .cantGetOnline {
                        Text(
                            "Golden path when browsers won’t load: Onramp gathers path, DNS, proxy, VPN, and live probes, then offers click-to-run next steps. After each step it re-diagnoses until you’re online — or until it can’t help further."
                        )
                        .foregroundStyle(.secondary)
                    }

                    HStack {
                        Button(isRunning ? "Diagnosing…" : "Run playbook") {
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
                        if result.looksOnline {
                            onlineBanner
                        }

                        TriageReportCard(report: result.triage)

                        if !result.actions.isEmpty, !result.looksOnline {
                            SuggestedActionsView(
                                actions: result.actions,
                                isRunningPlaybook: isRunning,
                                onRecheck: {
                                    Task { await run(selection) }
                                },
                                onActionOutput: { output in
                                    actionLog.append("### \(output.title)\n\n\(output.body)")
                                }
                            )
                        } else if result.looksOnline {
                            Text("Nothing else to do — probes succeeded. If one site still fails, try “Only some sites fail”.")
                                .foregroundStyle(.secondary)
                        }

                        if !actionLog.isEmpty {
                            DisclosureGroup("Steps you ran this session (\(actionLog.count))") {
                                ForEach(Array(actionLog.enumerated()), id: \.offset) { _, entry in
                                    Text(entry)
                                        .font(.caption.monospaced())
                                        .textSelection(.enabled)
                                        .padding(.vertical, 4)
                                }
                            }
                        }

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
                            "Run to get a ranked likely cause plus click-to-run next steps. Fixes that change Settings are done by you; probes are read-only."
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
                actionLog = []
            }
        } else {
            Text("Select a playbook")
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func header(for selection: ConnectivityPlaybookKind) -> some View {
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
    }

    private var onlineBanner: some View {
        HStack(spacing: 12) {
            Image(systemName: "checkmark.circle.fill")
                .foregroundStyle(.green)
                .font(.title2)
            VStack(alignment: .leading, spacing: 2) {
                Text("Back online")
                    .font(.headline)
                Text("Path, DNS, and probes look healthy. You’re done unless a specific site still fails.")
                    .font(.callout)
                    .foregroundStyle(.secondary)
            }
        }
        .padding(12)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(Color.green.opacity(0.12))
        .clipShape(RoundedRectangle(cornerRadius: 10))
        .accessibilityIdentifier("online-banner")
    }

    private func maybeAutoStart() async {
        guard autoStartCantGetOnline, !didAutoStart, onboarding.isCompleted || !onboarding.showReadyFlow else {
            return
        }
        didAutoStart = true
        selection = .cantGetOnline
        await run(.cantGetOnline)
    }

    private func run(_ kind: ConnectivityPlaybookKind) async {
        isRunning = true
        progress = "Starting…"
        defer { isRunning = false }
        let finished = await ConnectivityPlaybookRunner.run(kind: kind) { message in
            await MainActor.run {
                progress = message
            }
        }
        result = finished
        progress = finished.looksOnline ? "Online" : "Diagnosis ready — try a suggested step"
        showRawChecks = false
    }
}

#Preview {
    PlaybooksView()
        .environmentObject(FoundationModelsGateModel())
        .environmentObject(OnboardingModel())
}

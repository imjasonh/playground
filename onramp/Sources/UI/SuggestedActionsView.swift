import SwiftUI

/// Click-to-run next steps: confirm what will happen, run read-only probe / open
/// Settings, then optionally continue diagnosis with a full playbook recheck.
struct SuggestedActionsView: View {
    let actions: [SuggestedAction]
    var isRunningPlaybook: Bool
    var onRecheck: () -> Void
    var onActionOutput: ((SuggestedActionRunner.Result) -> Void)?

    @State private var pending: SuggestedAction?
    @State private var runningID: String?
    @State private var lastOutput: SuggestedActionRunner.Result?

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Fix & recheck")
                .font(.headline)
            Text("Each button explains what it will do. Diagnostics are read-only; Settings links open so you can change things yourself. After a probe, Onramp re-runs diagnosis with the new evidence.")
                .font(.callout)
                .foregroundStyle(.secondary)

            ForEach(actions) { action in
                actionRow(action)
            }

            if let lastOutput {
                VStack(alignment: .leading, spacing: 8) {
                    HStack {
                        Text("Last command output")
                            .font(.subheadline.weight(.semibold))
                        Spacer()
                        Button("Copy") {
                            PasteboardCopy.string(lastOutput.body)
                        }
                        .controlSize(.small)
                    }
                    ScrollView {
                        Text(lastOutput.body)
                            .font(.caption.monospaced())
                            .textSelection(.enabled)
                            .frame(maxWidth: .infinity, alignment: .leading)
                    }
                    .frame(maxHeight: 160)
                    if lastOutput.shouldRecheck {
                        Button("Continue diagnosis with this evidence") {
                            onRecheck()
                        }
                        .buttonStyle(.borderedProminent)
                        .disabled(isRunningPlaybook)
                        .accessibilityIdentifier("continue-diagnosis")
                    }
                }
                .padding(10)
                .background(Color.primary.opacity(0.04))
                .clipShape(RoundedRectangle(cornerRadius: 8))
            }
        }
        .sheet(item: $pending) { action in
            confirmSheet(action)
        }
        .accessibilityIdentifier("suggested-actions")
    }

    private func actionRow(_ action: SuggestedAction) -> some View {
        VStack(alignment: .leading, spacing: 6) {
            Text(action.title)
                .font(.body.weight(.semibold))
            Text(action.why)
                .font(.callout)
                .foregroundStyle(.secondary)
            Text(action.whatItDoes)
                .font(.caption)
                .foregroundStyle(.secondary)
            Button {
                pending = action
            } label: {
                if runningID == action.id {
                    Text("Running…")
                } else {
                    Text(action.kind == .recheck ? "Run full diagnosis" : "Review & run")
                }
            }
            .disabled(isRunningPlaybook || runningID != nil)
            .accessibilityIdentifier("action-\(action.id)")
        }
        .padding(10)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(Color.accentColor.opacity(0.06))
        .clipShape(RoundedRectangle(cornerRadius: 8))
    }

    private func confirmSheet(_ action: SuggestedAction) -> some View {
        VStack(alignment: .leading, spacing: 16) {
            Text(action.title)
                .font(.title2.weight(.semibold))
            labeled("Why", action.why)
            labeled("What it will do", action.whatItDoes)
            VStack(alignment: .leading, spacing: 4) {
                Text("Details")
                    .font(.subheadline.weight(.semibold))
                Text(action.confirmationDetail)
                    .font(.body.monospaced())
                    .textSelection(.enabled)
                    .padding(8)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .background(Color.primary.opacity(0.05))
                    .clipShape(RoundedRectangle(cornerRadius: 6))
            }
            Text(action.isReadOnly
                 ? "This step is read-only (or only opens Settings/browser). It will not change network configuration by itself."
                 : "Review carefully before continuing.")
                .font(.callout)
                .foregroundStyle(.secondary)

            HStack {
                Button("Cancel") {
                    pending = nil
                }
                .keyboardShortcut(.cancelAction)
                Spacer()
                Button(action.kind == .recheck ? "Run diagnosis" : "Run") {
                    Task { await execute(action) }
                }
                .buttonStyle(.borderedProminent)
                .keyboardShortcut(.defaultAction)
                .accessibilityIdentifier("confirm-run-action")
            }
        }
        .padding(24)
        .frame(minWidth: 420, idealWidth: 480)
    }

    private func labeled(_ title: String, _ body: String) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(title)
                .font(.subheadline.weight(.semibold))
            Text(body)
                .fixedSize(horizontal: false, vertical: true)
        }
    }

    private func execute(_ action: SuggestedAction) async {
        pending = nil
        runningID = action.id
        defer { runningID = nil }
        if case .recheck = action.kind {
            onRecheck()
            return
        }
        let result = await SuggestedActionRunner.run(action)
        lastOutput = result
        onActionOutput?(result)
        if result.shouldRecheck {
            // Auto-continue diagnosis after a probe — golden-path smoothness.
            onRecheck()
        }
    }
}

import SwiftUI

/// Detailed finding card used inside the Inspector window, with optional scoped AFM investigation.
struct FindingCardView: View {
    let finding: Finding
    let relatedDevice: LANDevice?
    let onAcknowledge: () -> Void
    let onMute: () -> Void
    let onTrustSubject: (() -> Void)?

    @State private var showInvestigate = false

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack(alignment: .top, spacing: 8) {
                Image(systemName: finding.severity.symbolName)
                    .foregroundStyle(severityColor)
                    .font(.title3)

                VStack(alignment: .leading, spacing: 3) {
                    HStack(spacing: 6) {
                        Text(finding.displayHeadline)
                            .font(.headline)
                        Text(finding.severity.label.uppercased())
                            .font(.caption2.weight(.bold))
                            .padding(.horizontal, 6)
                            .padding(.vertical, 2)
                            .background(severityColor.opacity(0.15), in: Capsule())
                            .foregroundStyle(severityColor)
                        if finding.explanation?.generatedByAFM == true {
                            Label("Apple Intelligence", systemImage: "sparkles")
                                .font(.caption2)
                                .foregroundStyle(.secondary)
                        }
                    }

                    Text(finding.displayBody)
                        .font(.callout)
                        .foregroundStyle(.primary)

                    if let step = finding.explanation?.nextStep, !step.isEmpty {
                        Text("Next step: \(step)")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                            .padding(.top, 2)
                    }
                }
                Spacer()
                Text(finding.lastSeen, style: .relative)
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }

            if !finding.evidence.isEmpty {
                VStack(alignment: .leading, spacing: 2) {
                    ForEach(finding.evidence, id: \.self) { line in
                        Text("• \(line)")
                            .font(.caption.monospaced())
                            .foregroundStyle(.secondary)
                    }
                }
                .padding(8)
                .frame(maxWidth: .infinity, alignment: .leading)
                .background(.quaternary.opacity(0.35), in: RoundedRectangle(cornerRadius: 6))
            }

            HStack(spacing: 8) {
                Button("Investigate…") {
                    showInvestigate = true
                }
                if let onTrustSubject {
                    Button("Trust", action: onTrustSubject)
                }
                Button("Mute Rule", action: onMute)
                if !finding.isAcknowledged {
                    Button("Dismiss", action: onAcknowledge)
                }
                Spacer()
            }
            .controlSize(.small)
        }
        .padding(12)
        .background(.background, in: RoundedRectangle(cornerRadius: 10))
        .overlay(
            RoundedRectangle(cornerRadius: 10)
                .stroke(.separator.opacity(0.5), lineWidth: 1)
        )
        .sheet(isPresented: $showInvestigate) {
            ScopedInvestigateSheet(finding: finding, relatedDevice: relatedDevice)
        }
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

/// Focused single-finding Q&A sheet backed by `ScopedInvestigator` (fresh session, <=3 tiny tools).
struct ScopedInvestigateSheet: View {
    let finding: Finding
    let relatedDevice: LANDevice?

    @Environment(\.dismiss) private var dismiss
    @State private var question = "Is this likely benign or suspicious, and should I re-check it right now?"
    @State private var answer: ScopedInvestigator.InvestigationAnswer?
    @State private var isRunning = false

    private let quickQuestions = [
        "Is this likely benign or suspicious?",
        "Re-probe this host or router live and tell me what's still open.",
        "Could this be a residential proxy or compromised IoT device?",
    ]

    var body: some View {
        VStack(alignment: .leading, spacing: 14) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("Investigate Finding")
                        .font(.title3.weight(.semibold))
                    Text(finding.displayHeadline)
                        .font(.callout)
                        .foregroundStyle(.secondary)
                }
                Spacer()
                Button("Done") { dismiss() }
            }

            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 6) {
                    ForEach(quickQuestions, id: \.self) { q in
                        Button(q) {
                            question = q
                            Task { await runInvestigation() }
                        }
                        .controlSize(.small)
                    }
                }
            }

            HStack {
                TextField("Ask about this specific finding…", text: $question)
                    .textFieldStyle(.roundedBorder)
                    .onSubmit { Task { await runInvestigation() } }
                Button(isRunning ? "Checking…" : "Ask") {
                    Task { await runInvestigation() }
                }
                .disabled(isRunning || question.trimmingCharacters(in: .whitespaces).isEmpty)
                .keyboardShortcut(.defaultAction)
            }

            if isRunning {
                HStack(spacing: 8) {
                    ProgressView().controlSize(.small)
                    Text("Running scoped check…")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            } else if let answer {
                ScrollView {
                    VStack(alignment: .leading, spacing: 8) {
                        Text(answer.text)
                            .font(.body)
                            .textSelection(.enabled)
                        HStack(spacing: 8) {
                            Text(answer.usedAFM ? "Apple Intelligence (scoped session)" : "Built-in analysis")
                                .font(.caption2)
                                .foregroundStyle(.secondary)
                            if !answer.usedTools.isEmpty {
                                Text("· Tools: \(answer.usedTools.joined(separator: ", "))")
                                    .font(.caption2)
                                    .foregroundStyle(.secondary)
                            }
                        }
                    }
                    .frame(maxWidth: .infinity, alignment: .leading)
                }
                .padding(10)
                .background(.quaternary.opacity(0.35), in: RoundedRectangle(cornerRadius: 8))
            }

            Spacer(minLength: 0)
        }
        .padding(18)
        .frame(width: 540, height: 380)
    }

    private func runInvestigation() async {
        isRunning = true
        defer { isRunning = false }
        answer = await ScopedInvestigator.answer(
            question: question,
            finding: finding,
            relatedDevice: relatedDevice
        )
    }
}

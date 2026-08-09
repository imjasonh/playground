import SwiftUI

/// Walks the App Attest → App Check → Firebase Auth → Workload Identity chain and
/// shows what each exchange produced.
struct GCPAuthView: View {
    @StateObject private var model = GCPAuthFlowModel()

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                modeBanner
                premise
                steps
                controls
                statusLine
                if !model.tokens.isEmpty {
                    inspector
                }
                caveat
            }
            .padding()
        }
        .navigationTitle("GCP Auth")
    }

    private var modeBanner: some View {
        HStack(spacing: 8) {
            Image(systemName: model.isSimulated ? "theatermasks" : "antenna.radiowaves.left.and.right")
            Text(model.isSimulated ? "Simulated — no project, no network" : "Live — \(model.configuration.projectID)")
                .font(.footnote.weight(.semibold))
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 6)
        .background(
            RoundedRectangle(cornerRadius: 8, style: .continuous)
                .fill(model.isSimulated ? Color.orange.opacity(0.18) : Color.green.opacity(0.18))
        )
        .accessibilityIdentifier("gcpAuthModeBadge")
    }

    private var premise: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("The app ships no credential")
                .font(.headline)
            Text("""
                An iOS app cannot keep a secret — anything in the binary is \
                extractable. So nothing here is shipped: the only private key \
                involved is generated inside this device's Secure Enclave and \
                cannot leave it, and every token below expires within the hour.
                """)
            .font(.callout)
            .foregroundStyle(.secondary)
        }
    }

    private var steps: some View {
        VStack(spacing: 12) {
            ForEach(GCPAuthStep.allCases) { step in
                stepRow(step)
            }
        }
    }

    private func stepRow(_ step: GCPAuthStep) -> some View {
        let state = model.state(for: step)
        return HStack(alignment: .top, spacing: 12) {
            Group {
                if state == .running {
                    ProgressView()
                } else {
                    Image(systemName: state.symbolName)
                        .foregroundStyle(tint(for: state))
                }
            }
            .frame(width: 22)

            VStack(alignment: .leading, spacing: 4) {
                Text(step.title)
                    .font(.subheadline.weight(.semibold))
                Text(step.detail)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                if let outcome = outcomeText(state) {
                    Text(outcome)
                        .font(.system(.caption, design: .monospaced))
                        .foregroundStyle(tint(for: state))
                        .textSelection(.enabled)
                }
            }
            Spacer(minLength: 0)
        }
        .padding(12)
        .background(
            RoundedRectangle(cornerRadius: 12, style: .continuous)
                .fill(Color.secondary.opacity(0.08))
        )
        .accessibilityIdentifier("gcpAuthStep-\(step.rawValue)")
    }

    private var controls: some View {
        HStack(spacing: 12) {
            Button {
                Task { await model.run() }
            } label: {
                Text(model.isRunning ? "Running…" : "Run the chain")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.borderedProminent)
            .disabled(model.isRunning)
            .accessibilityIdentifier("gcpAuthRunButton")

            Button("Reset") {
                model.reset()
            }
            .buttonStyle(.bordered)
            .disabled(model.isRunning)
            .accessibilityIdentifier("gcpAuthResetButton")
        }
    }

    private var statusLine: some View {
        Text(model.statusMessage)
            .font(.footnote)
            .foregroundStyle(.secondary)
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("gcpAuthStatusMessage")
    }

    private var inspector: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("What the tokens say")
                .font(.headline)
            Text("Decoded locally, never verified — signature checks belong on the server that consumes the token.")
                .font(.caption)
                .foregroundStyle(.secondary)

            ForEach(GCPAuthStep.allCases) { step in
                if let claims = model.claims(for: step) {
                    DisclosureGroup(step.title) {
                        VStack(alignment: .leading, spacing: 4) {
                            ForEach(claims.all) { claim in
                                HStack(alignment: .top, spacing: 6) {
                                    Text(claim.name)
                                        .font(.system(.caption2, design: .monospaced).weight(.semibold))
                                        .frame(width: 110, alignment: .leading)
                                    Text(claim.value)
                                        .font(.system(.caption2, design: .monospaced))
                                        .foregroundStyle(.secondary)
                                }
                            }
                        }
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(.top, 4)
                    }
                    .font(.subheadline)
                } else if let token = model.tokens[step] {
                    // The Google access token is opaque, not a JWT.
                    HStack {
                        Text(step.title).font(.subheadline)
                        Spacer()
                        Text(token.redacted)
                            .font(.system(.caption2, design: .monospaced))
                            .foregroundStyle(.secondary)
                    }
                }
            }
        }
        .accessibilityIdentifier("gcpAuthTokenInspector")
    }

    private var caveat: some View {
        VStack(alignment: .leading, spacing: 6) {
            Label("Federating straight from the client is the weaker option", systemImage: "exclamationmark.triangle")
                .font(.subheadline.weight(.semibold))
            Text("""
                Google's STS validates the Firebase ID token — it does not look at \
                App Check. Attestation is enforced by Firebase Auth and by \
                whatever backend you write, so a design where the app calls your \
                own service and never holds Google credentials keeps the \
                attestation in the enforcement path and shrinks the blast radius \
                to one user.
                """)
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .padding(12)
        .background(
            RoundedRectangle(cornerRadius: 12, style: .continuous)
                .fill(Color.yellow.opacity(0.12))
        )
    }

    private func tint(for state: GCPAuthStepState) -> Color {
        switch state {
        case .pending: return .secondary
        case .running: return .accentColor
        case .succeeded: return .green
        case .failed: return .red
        }
    }

    private func outcomeText(_ state: GCPAuthStepState) -> String? {
        switch state {
        case .succeeded(let message), .failed(let message):
            return message
        case .pending, .running:
            return nil
        }
    }
}

#Preview {
    NavigationStack {
        GCPAuthView()
    }
}

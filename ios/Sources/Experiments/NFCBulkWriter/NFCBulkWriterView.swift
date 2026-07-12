import SwiftUI

/// Bulk-write UI: edit one NDEF payload, then tap tags until you stop.
struct NFCBulkWriterView: View {
    @StateObject private var session = NFCBulkWriterSession()
    @State private var draft = NFCBulkPayloadDraft(kind: .url, text: "")
    @FocusState private var payloadFocused: Bool

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 20) {
                intro
                payloadEditor
                counters
                controls
                status
                howItWorks
            }
            .padding()
        }
        .onDisappear {
            if session.isScanning {
                session.stop()
            }
        }
    }

    private var intro: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("Write many tags")
                .font(.title2.bold())
            Text("Choose Text or URL, start writing, then hold each tag to the iPhone. The same payload is applied until you stop or leave.")
                .font(.subheadline)
                .foregroundStyle(.secondary)
        }
        .accessibilityElement(children: .combine)
    }

    private var payloadEditor: some View {
        VStack(alignment: .leading, spacing: 12) {
            Picker("Payload type", selection: $draft.kind) {
                ForEach(NFCBulkPayloadKind.allCases) { kind in
                    Text(kind.title).tag(kind)
                }
            }
            .pickerStyle(.segmented)
            .disabled(session.isScanning)
            .accessibilityIdentifier("nfcPayloadKindPicker")

            Text(draft.kind.fieldLabel)
                .font(.footnote.weight(.semibold))
                .foregroundStyle(.secondary)

            TextField(draft.kind.placeholder, text: $draft.text, axis: .vertical)
                .textFieldStyle(.roundedBorder)
                .lineLimit(3...6)
                .disabled(session.isScanning)
                .focused($payloadFocused)
                .textInputAutocapitalization(draft.kind == .url ? .never : .sentences)
                .keyboardType(draft.kind == .url ? .URL : .default)
                .autocorrectionDisabled(draft.kind == .url)
                .accessibilityIdentifier("nfcPayloadTextField")

            if let error = draft.validationError, !draft.isEmpty {
                Text(error)
                    .font(.caption)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("nfcPayloadValidationMessage")
            }
        }
    }

    private var counters: some View {
        HStack(spacing: 12) {
            counterCard(title: "Written", value: "\(session.writtenCount)", identifier: "nfcWrittenCount")
            counterCard(title: "Failed", value: "\(session.failedCount)", identifier: "nfcFailedCount")
        }
    }

    private func counterCard(title: String, value: String, identifier: String) -> some View {
        VStack(spacing: 4) {
            Text(value)
                .font(.title.monospacedDigit().bold())
                .accessibilityIdentifier(identifier)
            Text(title)
                .font(.caption)
                .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity)
        .padding(.vertical, 12)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 12))
    }

    private var controls: some View {
        Group {
            if session.isScanning {
                Button(role: .destructive) {
                    payloadFocused = false
                    session.stop()
                } label: {
                    Label("Stop writing", systemImage: "stop.circle.fill")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("stopNFCBulkWriteButton")
            } else {
                Button {
                    payloadFocused = false
                    session.start(with: draft)
                } label: {
                    Label("Start writing", systemImage: "wave.3.right")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!draft.isValid || !session.isNFCAvailable)
                .accessibilityIdentifier("startNFCBulkWriteButton")
            }
        }
    }

    private var status: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("nfcBulkWriterStatusMessage")

            if let outcome = session.lastOutcome {
                Text(outcome)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("nfcBulkWriterLastOutcome")
            }

            if !session.isNFCAvailable {
                Text("This device can’t write NFC tags. Use a physical iPhone with NFC — Simulator can’t run CoreNFC sessions.")
                    .font(.caption)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("nfcUnavailableMessage")
            }
        }
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("How it works")
                .font(.headline)
            Text("• URL payloads are stored as well-known URI records (bare hosts get https://).")
            Text("• Text payloads use a well-known Text record (English locale).")
            Text("• Read-only or non-NDEF tags are skipped and counted as failed.")
            Text("• Leaving this screen stops the session.")
        }
        .font(.footnote)
        .foregroundStyle(.secondary)
        .frame(maxWidth: .infinity, alignment: .leading)
        .padding(.top, 8)
    }
}

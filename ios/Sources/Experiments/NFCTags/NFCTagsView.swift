import SwiftUI

/// Read and write NFC tags (NDEF text/URL). Needs a physical iPhone; Simulator opens the UI only.
struct NFCTagsView: View {
    @StateObject private var controller = NFCTagsController()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner

                Picker("Mode", selection: $controller.mode) {
                    Text("Read").tag(NFCTagsController.Mode.read)
                    Text("Write").tag(NFCTagsController.Mode.write)
                }
                .pickerStyle(.segmented)
                .accessibilityIdentifier("nfcModePicker")

                if controller.mode == .write {
                    writeForm
                } else {
                    readResults
                }

                actionButtons

                Text(controller.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: .infinity)
                    .accessibilityIdentifier("nfcStatusMessage")

                howItWorks
            }
            .padding()
        }
        .onDisappear {
            controller.cancelSession()
        }
    }

    private var availabilityBanner: some View {
        Group {
            if controller.isNFCAvailable {
                Label("NFC reader ready", systemImage: "checkmark.circle.fill")
                    .foregroundStyle(.green)
            } else {
                Label(
                    "NFC needs a physical iPhone. The Simulator cannot scan tags.",
                    systemImage: "iphone.slash"
                )
                .foregroundStyle(.orange)
            }
        }
        .font(.subheadline)
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("nfcAvailabilityBanner")
    }

    private var writeForm: some View {
        VStack(alignment: .leading, spacing: 12) {
            Picker("Content", selection: $controller.draft.kind) {
                ForEach(NFCNDEFContentKind.allCases) { kind in
                    Text(kind.title).tag(kind)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("nfcWriteKindPicker")

            TextField(
                controller.draft.kind == .url ? "https://example.com" : "Text to write",
                text: $controller.draft.text,
                axis: .vertical
            )
            .lineLimit(3...6)
            .textFieldStyle(.roundedBorder)
            .textInputAutocapitalization(controller.draft.kind == .url ? .never : .sentences)
            .keyboardType(controller.draft.kind == .url ? .URL : .default)
            .autocorrectionDisabled(controller.draft.kind == .url)
            .accessibilityIdentifier("nfcWriteTextField")
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var readResults: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Last read")
                .font(.subheadline.bold())
            if controller.lastReadSummary.isEmpty {
                Text("No tag scanned yet.")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("nfcReadPlaceholder")
            } else {
                Text(controller.lastReadSummary)
                    .font(.body.monospaced())
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(12)
                    .background(Color.secondary.opacity(0.12), in: RoundedRectangle(cornerRadius: 10))
                    .accessibilityIdentifier("nfcReadSummary")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var actionButtons: some View {
        VStack(spacing: 10) {
            if controller.isSessionActive {
                Button(role: .destructive) {
                    controller.cancelSession()
                } label: {
                    Label("Cancel scan", systemImage: "xmark.circle.fill")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("nfcCancelScanButton")
            } else if controller.mode == .read {
                Button {
                    controller.startRead()
                } label: {
                    Label("Scan tag", systemImage: "wave.3.right")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!controller.isNFCAvailable)
                .accessibilityIdentifier("nfcScanButton")
            } else {
                Button {
                    controller.startWrite()
                } label: {
                    Label("Write to tag", systemImage: "square.and.pencil")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!controller.isNFCAvailable)
                .accessibilityIdentifier("nfcWriteButton")
            }
        }
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.subheadline.bold())
            Text(
                "Reads and writes NDEF Text and URL records. Blank NTAG / Type 2 tags show as "
                    + "empty (with UID) instead of an error; switch to Write to store content. "
                    + "Many transit and product tags are locked read-only."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
            if let build = Bundle.main.object(forInfoDictionaryKey: "CFBundleVersion") as? String {
                Text("Build \(build)")
                    .font(.caption2)
                    .foregroundStyle(.tertiary)
                    .accessibilityIdentifier("nfcBuildNumber")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }
}

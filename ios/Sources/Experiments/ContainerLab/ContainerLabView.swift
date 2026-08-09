import SwiftUI

/// Container Lab: name a container image, pull it to an on-device OCI layout,
/// and see whether this device can host the wasm runtime that would run it.
struct ContainerLabView: View {
    @StateObject private var model = ContainerLabModel()

    var body: some View {
        List {
            imageSection
            statusSection
            if let resolved = model.resolved {
                resolvedSection(resolved)
                layersSection
                pullSection
            }
            runtimeSection
            aboutSection
        }
        .navigationTitle("Container Lab")
        .navigationBarTitleDisplayMode(.inline)
    }

    // MARK: - Sections

    private var imageSection: some View {
        Section("Image") {
            TextField("alpine:3.20", text: $model.imageText)
                .textInputAutocapitalization(.never)
                .autocorrectionDisabled()
                .keyboardType(.URL)
                .font(.system(.body, design: .monospaced))
                .accessibilityIdentifier("containerLabImageField")

            Picker("Platform", selection: $model.architecture) {
                ForEach(TargetArchitecture.allCases) { architecture in
                    Text(architecture.label).tag(architecture)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("containerLabArchPicker")

            Button {
                Task { await model.inspect() }
            } label: {
                Label("Resolve & inspect", systemImage: "magnifyingglass")
            }
            .disabled(model.isBusy)
            .accessibilityIdentifier("containerLabInspectButton")
        }
    }

    private var statusSection: some View {
        Section {
            HStack(spacing: 8) {
                if model.isBusy {
                    ProgressView()
                }
                Text(model.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            }
            .accessibilityIdentifier("containerLabStatusMessage")

            if let errorMessage = model.errorMessage {
                Text(errorMessage)
                    .font(.footnote)
                    .foregroundStyle(.red)
                    .accessibilityIdentifier("containerLabErrorMessage")
            }
        }
    }

    private func resolvedSection(_ resolved: ResolvedImage) -> some View {
        Section("Resolved") {
            detailRow("Reference", resolved.reference.canonicalName)
            detailRow("Platform", resolved.platform.displayName)
            detailRow("Manifest", shortDigest(resolved.manifestDescriptor.digest))
            detailRow("Config", shortDigest(resolved.manifest.config.digest))
            if !resolved.config.commandLine.isEmpty {
                detailRow("Command", resolved.config.commandLine.joined(separator: " "))
            }
            if let workingDir = resolved.config.config?.workingDir, !workingDir.isEmpty {
                detailRow("Workdir", workingDir)
            }
        }
    }

    private var layersSection: some View {
        Section("Layers") {
            ForEach(model.layerRows) { layer in
                HStack {
                    Text("\(layer.index)")
                        .font(.caption.monospacedDigit())
                        .foregroundStyle(.secondary)
                        .frame(width: 20, alignment: .leading)
                    VStack(alignment: .leading, spacing: 2) {
                        Text(layer.shortDigest)
                            .font(.system(.footnote, design: .monospaced))
                        Text(layer.isCompressed ? "gzip" : "uncompressed")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                    Spacer()
                    Text(ContainerLabModel.byteFormatter.string(fromByteCount: layer.size))
                        .font(.caption.monospacedDigit())
                        .foregroundStyle(.secondary)
                }
            }
        }
    }

    private var pullSection: some View {
        Section("On-device layout") {
            Button {
                Task { await model.materialize() }
            } label: {
                Label("Pull to OCI layout", systemImage: "arrow.down.circle")
            }
            .disabled(model.isBusy)
            .accessibilityIdentifier("containerLabPullButton")

            if let materialized = model.materialized {
                detailRow("Manifest", shortDigest(materialized.manifestDigest))
                detailRow("Layers", "\(materialized.layerCount) (\(materialized.decompressedLayerCount) inflated)")
                detailRow("On disk", ContainerLabModel.byteFormatter.string(fromByteCount: materialized.bytesOnDisk))
                Text(materialized.root.lastPathComponent)
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("containerLabLayoutPath")
            }
        }
    }

    private var runtimeSection: some View {
        Section("Runtime") {
            Text(model.runtimeStatus)
                .font(.footnote)
                .foregroundStyle(model.isRuntimeInstalled ? Color.secondary : Color.orange)
                .accessibilityIdentifier("containerLabRuntimeStatus")

            Button {
                Task { await model.checkIsolation() }
            } label: {
                Label("Check webview isolation", systemImage: "checkmark.shield")
            }
            .disabled(model.isBusy)
            .accessibilityIdentifier("containerLabIsolationButton")

            Text(model.isolationMessage)
                .font(.footnote)
                .foregroundStyle(isolationColor)
                .accessibilityIdentifier("containerLabIsolationMessage")
        }
    }

    private var aboutSection: some View {
        Section("How this works") {
            Text("""
            iOS will not execute an image's binaries: every executable page has to be \
            signed by Apple, and that is true even though the phone is already arm64. \
            The only sanctioned JIT on the device belongs to WebKit, so the plan is to \
            pull and unpack the image natively here, serve it from a loopback origin \
            that sets the cross-origin isolation headers, and let a wasm CPU emulator \
            inside a WKWebView actually run it.
            """)
            .font(.footnote)
            .foregroundStyle(.secondary)
        }
    }

    // MARK: - Bits

    private var isolationColor: Color {
        guard let isolation = model.isolation else { return .secondary }
        return isolation.isRuntimeCapable ? .green : .orange
    }

    private func detailRow(_ label: String, _ value: String) -> some View {
        HStack(alignment: .firstTextBaseline) {
            Text(label)
                .font(.footnote)
                .foregroundStyle(.secondary)
            Spacer()
            Text(value)
                .font(.system(.footnote, design: .monospaced))
                .multilineTextAlignment(.trailing)
        }
    }

    private func shortDigest(_ digest: String) -> String {
        guard let hex = OCIDigest.hex(digest) else { return digest }
        return String(hex.prefix(16))
    }
}

#Preview {
    NavigationStack {
        ContainerLabView()
    }
}

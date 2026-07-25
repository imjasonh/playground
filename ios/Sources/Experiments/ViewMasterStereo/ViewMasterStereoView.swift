import SwiftUI

/// View-Master stereo camera — dual-wide capture with level gate + wigglegram.
struct ViewMasterStereoView: View {
    @StateObject private var session = ViewMasterStereoSession()
    @State private var isExportingGIF = false
    @State private var shareItem: ShareItem?
    @State private var exportError: String?

    var body: some View {
        VStack(spacing: 0) {
            stage
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .background(Color.black)

            controls
                .padding()
                .background(.ultraThinMaterial)
        }
        .onAppear { session.start() }
        .onDisappear { session.stop() }
        .sheet(item: $shareItem, onDismiss: clearShareItem) { item in
            ShareSheet(items: [item.url], onComplete: clearShareItem)
        }
    }

    @ViewBuilder
    private var stage: some View {
        if let pair = session.capturedPair {
            capturedStage(pair)
        } else {
            liveStage
        }
    }

    private var liveStage: some View {
        GeometryReader { geo in
            ZStack {
                if let image = session.previewImage {
                    Image(uiImage: image)
                        .resizable()
                        .scaledToFill()
                        .frame(width: geo.size.width, height: geo.size.height)
                        .clipped()
                        .accessibilityIdentifier("viewMasterLivePreview")
                } else {
                    placeholder
                        .frame(width: geo.size.width, height: geo.size.height)
                }

                VStack {
                    Spacer()
                    readinessBanner
                        .padding(.bottom, 16)
                }
            }
        }
    }

    private func capturedStage(_ pair: StereoPairAligner.Pair) -> some View {
        VStack(spacing: 12) {
            Picker("Preview", selection: $session.previewMode) {
                ForEach(ViewMasterStereoSession.PreviewMode.allCases) { mode in
                    Text(mode.title).tag(mode)
                }
            }
            .pickerStyle(.segmented)
            .padding(.horizontal)
            .padding(.top, 12)
            .accessibilityIdentifier("viewMasterPreviewMode")

            Group {
                switch session.previewMode {
                case .sideBySide:
                    sideBySide(pair)
                case .wigglegram:
                    WigglegramView(left: pair.left, right: pair.right)
                        .padding(.horizontal)
                }
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func sideBySide(_ pair: StereoPairAligner.Pair) -> some View {
        HStack(spacing: 8) {
            eyeCard(title: "Left", image: pair.left, id: "viewMasterLeftEye")
            eyeCard(title: "Right", image: pair.right, id: "viewMasterRightEye")
        }
        .padding(.horizontal)
    }

    private func eyeCard(title: String, image: UIImage, id: String) -> some View {
        VStack(spacing: 6) {
            Text(title)
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
            Image(uiImage: image)
                .resizable()
                .scaledToFit()
                .clipShape(RoundedRectangle(cornerRadius: 8, style: .continuous))
                .accessibilityIdentifier(id)
        }
        .frame(maxWidth: .infinity)
    }

    private var readinessBanner: some View {
        let ready = session.readiness.canCapture
        return Text(ready ? "Landscape · Level" : session.readiness.blockingReason)
            .font(.subheadline.weight(.semibold))
            .padding(.horizontal, 14)
            .padding(.vertical, 8)
            .background(ready ? Color.green.opacity(0.85) : Color.orange.opacity(0.9), in: Capsule())
            .foregroundStyle(.white)
            .accessibilityIdentifier("viewMasterReadinessBanner")
    }

    private var placeholder: some View {
        VStack(spacing: 12) {
            Image(systemName: placeholderSymbol)
                .font(.system(size: 48))
                .foregroundStyle(.white.opacity(0.85))
            Text(placeholderTitle)
                .font(.headline)
                .foregroundStyle(.white)
                .multilineTextAlignment(.center)
            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.white.opacity(0.7))
                .multilineTextAlignment(.center)
                .padding(.horizontal, 24)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .background(
            LinearGradient(
                colors: [
                    Color(red: 0.08, green: 0.1, blue: 0.16),
                    Color(red: 0.02, green: 0.03, blue: 0.06),
                ],
                startPoint: .topLeading,
                endPoint: .bottomTrailing
            )
        )
    }

    private var controls: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("viewMasterStatusMessage")

            if session.capturedPair != nil {
                HStack(spacing: 10) {
                    Button("Retake") {
                        session.clearCapture()
                        exportError = nil
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.large)
                    .frame(maxWidth: .infinity)
                    .accessibilityIdentifier("viewMasterRetakeButton")

                    Button {
                        exportWiggleGIF()
                    } label: {
                        if isExportingGIF {
                            ProgressView()
                                .frame(maxWidth: .infinity)
                        } else {
                            Label("Save GIF", systemImage: "square.and.arrow.down")
                                .frame(maxWidth: .infinity)
                        }
                    }
                    .buttonStyle(.borderedProminent)
                    .controlSize(.large)
                    .disabled(isExportingGIF)
                    .accessibilityIdentifier("viewMasterSaveGIFButton")
                }

                if let exportError {
                    Text(exportError)
                        .font(.caption)
                        .foregroundStyle(.red)
                        .accessibilityIdentifier("viewMasterGIFExportError")
                }
            } else {
                Button {
                    session.capture()
                } label: {
                    Label("Capture stereo pair", systemImage: "camera.aperture")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!session.canCapture)
                .accessibilityIdentifier("viewMasterCaptureButton")
            }
        }
    }

    private func exportWiggleGIF() {
        guard let pair = session.capturedPair, !isExportingGIF else { return }
        isExportingGIF = true
        exportError = nil
        let left = pair.left
        let right = pair.right
        DispatchQueue.global(qos: .userInitiated).async {
            do {
                let url = try WiggleGIFEncoder.writeTemporaryWiggleGIF(left: left, right: right)
                DispatchQueue.main.async {
                    self.isExportingGIF = false
                    self.shareItem = ShareItem(url: url)
                    self.session.setStatusMessage("Wiggle GIF ready — save or share it.")
                }
            } catch {
                DispatchQueue.main.async {
                    self.isExportingGIF = false
                    self.exportError = error.localizedDescription
                }
            }
        }
    }

    private func clearShareItem() {
        if let shareItem {
            try? FileManager.default.removeItem(at: shareItem.url)
        }
        shareItem = nil
    }

    private var placeholderSymbol: String {
        switch session.runState {
        case .permissionDenied: return "lock.slash"
        case .unsupported: return "camera.badge.ellipsis"
        case .failed: return "exclamationmark.triangle"
        default: return "rectangle.on.rectangle.angled"
        }
    }

    private var placeholderTitle: String {
        switch session.runState {
        case .permissionDenied: return "Camera access needed"
        case .unsupported: return "Dual-wide stereo unavailable"
        case .failed: return "Camera error"
        case .requestingPermission: return "Requesting access…"
        default: return "View-Master Stereo"
        }
    }
}

private struct ShareItem: Identifiable {
    let id = UUID()
    let url: URL
}


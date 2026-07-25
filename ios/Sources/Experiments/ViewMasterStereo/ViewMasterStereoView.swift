import SwiftUI

/// View-Master stereo camera — dual-wide capture with level gate + wigglegram.
struct ViewMasterStereoView: View {
    @StateObject private var session = ViewMasterStereoSession()
    @State private var isExportingGIF = false
    @State private var shareItem: ShareItem?
    @State private var exportError: String?

    var body: some View {
        GeometryReader { geo in
            let landscape = geo.size.width > geo.size.height
            ZStack {
                Color.black

                if let pair = session.capturedPair {
                    capturedStage(pair)
                    reviewChrome
                } else {
                    liveStage(size: geo.size)
                    liveChrome(landscape: landscape)
                }
            }
            .frame(width: geo.size.width, height: geo.size.height)
        }
        .background(Color.black)
        .ignoresSafeArea()
        .navigationBarTitleDisplayMode(.inline)
        .toolbarBackground(.hidden, for: .navigationBar)
        .toolbarColorScheme(.dark, for: .navigationBar)
        .onAppear { session.start() }
        .onDisappear { session.stop() }
        .sheet(item: $shareItem, onDismiss: clearShareItem) { item in
            ShareSheet(items: [item.url], onComplete: clearShareItem)
        }
    }

    // MARK: - Live (full-bleed)

    private func liveStage(size: CGSize) -> some View {
        Group {
            if let image = session.previewImage {
                Image(uiImage: image)
                    .resizable()
                    .scaledToFill()
                    .frame(width: size.width, height: size.height)
                    .clipped()
                    .accessibilityIdentifier("viewMasterLivePreview")
            } else {
                placeholder
                    .frame(width: size.width, height: size.height)
            }
        }
    }

    private func liveChrome(landscape: Bool) -> some View {
        ZStack {
            VStack {
                readinessBanner
                    .padding(.top, 56)
                Spacer()
                if !landscape {
                    Text(session.statusMessage)
                        .font(.footnote.weight(.medium))
                        .multilineTextAlignment(.center)
                        .foregroundStyle(.white)
                        .padding(.horizontal, 20)
                        .padding(.vertical, 10)
                        .background(.black.opacity(0.45), in: Capsule())
                        .padding(.bottom, 28)
                        .accessibilityIdentifier("viewMasterStatusMessage")
                }
            }

            if landscape {
                HStack {
                    Spacer()
                    shutterButton
                        .padding(.trailing, 18)
                }
            } else {
                // Portrait: keep a small shutter so UI tests / accessibility still
                // find it, but capture stays gated on landscape+level.
                VStack {
                    Spacer()
                    shutterButton
                        .padding(.bottom, 88)
                }
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var shutterButton: some View {
        Button {
            session.capture()
        } label: {
            ZStack {
                Circle()
                    .fill(.white.opacity(session.canCapture ? 0.95 : 0.35))
                    .frame(width: 64, height: 64)
                    .shadow(color: .black.opacity(0.35), radius: 8, y: 2)
                Circle()
                    .strokeBorder(.white.opacity(0.9), lineWidth: 3)
                    .frame(width: 74, height: 74)
            }
            .frame(width: 74, height: 74)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .disabled(!session.canCapture)
        .accessibilityLabel("Capture stereo pair")
        .accessibilityIdentifier("viewMasterCaptureButton")
    }

    // MARK: - Review

    private func capturedStage(_ pair: StereoPairAligner.Pair) -> some View {
        GeometryReader { geo in
            switch session.previewMode {
            case .sideBySide:
                sideBySide(pair, in: geo.size)
            case .wigglegram:
                StereoFillImage(reference: pair.left) {
                    WigglegramView(left: pair.left, right: pair.right)
                }
                .frame(width: geo.size.width, height: geo.size.height)
            }
        }
    }

    private var reviewChrome: some View {
        VStack(spacing: 0) {
            Spacer()
            VStack(alignment: .leading, spacing: 10) {
                Picker("Preview", selection: $session.previewMode) {
                    ForEach(ViewMasterStereoSession.PreviewMode.allCases) { mode in
                        Text(mode.title).tag(mode)
                    }
                }
                .pickerStyle(.segmented)
                .accessibilityIdentifier("viewMasterPreviewMode")

                Text(session.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.white.opacity(0.9))
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("viewMasterStatusMessage")

                HStack(spacing: 10) {
                    Button("Retake") {
                        session.clearCapture()
                        exportError = nil
                    }
                    .buttonStyle(.bordered)
                    .tint(.white)
                    .controlSize(.large)
                    .frame(maxWidth: .infinity)
                    .accessibilityIdentifier("viewMasterRetakeButton")

                    Button {
                        exportWiggleGIF()
                    } label: {
                        if isExportingGIF {
                            ProgressView()
                                .tint(.white)
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
            }
            .padding(14)
            .background(.ultraThinMaterial, in: RoundedRectangle(cornerRadius: 18, style: .continuous))
            .padding(.horizontal, 12)
            .padding(.bottom, 20)
        }
    }

    private func sideBySide(_ pair: StereoPairAligner.Pair, in size: CGSize) -> some View {
        let portrait = size.height > size.width
        return Group {
            if portrait {
                VStack(spacing: 10) {
                    eyeCard(title: "Left", image: pair.left, id: "viewMasterLeftEye")
                    eyeCard(title: "Right", image: pair.right, id: "viewMasterRightEye")
                }
                .padding(12)
            } else {
                HStack(spacing: 10) {
                    eyeCard(title: "Left", image: pair.left, id: "viewMasterLeftEye")
                    eyeCard(title: "Right", image: pair.right, id: "viewMasterRightEye")
                }
                .padding(12)
            }
        }
        .frame(width: size.width, height: size.height)
    }

    private func eyeCard(title: String, image: UIImage, id: String) -> some View {
        VStack(spacing: 6) {
            Text(title)
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
            Image(uiImage: image)
                .resizable()
                .scaledToFill()
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .clipped()
                .clipShape(RoundedRectangle(cornerRadius: 10, style: .continuous))
                .accessibilityIdentifier(id)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
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

    // MARK: - Export

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

/// Fills the container with a landscape stereo frame; rotates 90° when the
/// phone is portrait so capture previews aren't a tiny letterboxed strip.
private struct StereoFillImage<Content: View>: View {
    let reference: UIImage
    @ViewBuilder var content: () -> Content

    var body: some View {
        GeometryReader { geo in
            let landscapeImage = reference.size.width >= reference.size.height
            let portraitBox = geo.size.height > geo.size.width * 1.05

            if landscapeImage && portraitBox {
                content()
                    .frame(width: geo.size.height, height: geo.size.width)
                    .rotationEffect(.degrees(90))
                    .frame(width: geo.size.width, height: geo.size.height)
                    .clipped()
            } else {
                content()
                    .frame(width: geo.size.width, height: geo.size.height)
                    .clipped()
            }
        }
    }
}

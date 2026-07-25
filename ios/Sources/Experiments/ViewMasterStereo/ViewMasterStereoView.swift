import SwiftUI

/// View-Master stereo camera — dual-wide capture with level gate + wigglegram.
struct ViewMasterStereoView: View {
    @StateObject private var session = ViewMasterStereoSession()

    var body: some View {
        VStack(spacing: 0) {
            stage
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .background(Color.black)

            controls
                .padding(.horizontal, 16)
                .padding(.vertical, 12)
                .background(.ultraThinMaterial)
        }
        .onAppear { session.start() }
        .onDisappear { session.stop() }
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
                        .padding(.bottom, 20)
                }
            }
        }
    }

    private func capturedStage(_ pair: StereoPairAligner.Pair) -> some View {
        GeometryReader { geo in
            switch session.previewMode {
            case .sideBySide:
                sideBySide(pair, in: geo.size)
            case .wigglegram:
                StereoFillImage(image: pair.left) {
                    // Wigglegram swaps the UIImage; keep fill behavior identical.
                    WigglegramView(left: pair.left, right: pair.right)
                }
                .frame(width: geo.size.width, height: geo.size.height)
            }
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

    private var controls: some View {
        VStack(alignment: .leading, spacing: 10) {
            if session.capturedPair != nil {
                Picker("Preview", selection: $session.previewMode) {
                    ForEach(ViewMasterStereoSession.PreviewMode.allCases) { mode in
                        Text(mode.title).tag(mode)
                    }
                }
                .pickerStyle(.segmented)
                .accessibilityIdentifier("viewMasterPreviewMode")
            }

            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("viewMasterStatusMessage")

            if session.capturedPair != nil {
                Button("Retake") {
                    session.clearCapture()
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.large)
                .frame(maxWidth: .infinity)
                .accessibilityIdentifier("viewMasterRetakeButton")
            } else {
                Button {
                    session.capture()
                } label: {
                    Label("Capture stereo pair", systemImage: "camera.aperture")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.large)
                .disabled(!session.canCapture)
                .accessibilityIdentifier("viewMasterCaptureButton")
            }
        }
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

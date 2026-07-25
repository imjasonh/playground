import SwiftUI

/// Wigglecam — dual-wide wigglegram capture with a full-bleed shutter.
struct WigglecamView: View {
    @StateObject private var session = WigglecamSession()
    @State private var isSavingGIF = false
    @State private var saveFlash: String?
    @State private var saveError: String?

    var body: some View {
        GeometryReader { geo in
            let landscape = geo.size.width > geo.size.height
            ZStack {
                Color.black

                if let pair = session.capturedPair {
                    StereoFillImage(reference: pair.left) {
                        WigglegramView(left: pair.left, right: pair.right)
                    }
                    .frame(width: geo.size.width, height: geo.size.height)
                    .accessibilityIdentifier("wigglecamPreview")

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
    }

    // MARK: - Live

    private func liveStage(size: CGSize) -> some View {
        Group {
            if let image = session.previewImage {
                Image(uiImage: image)
                    .resizable()
                    .scaledToFill()
                    .frame(width: size.width, height: size.height)
                    .clipped()
                    .accessibilityIdentifier("wigglecamLivePreview")
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
                        .accessibilityIdentifier("wigglecamStatusMessage")
                }
            }

            if landscape {
                HStack {
                    Spacer()
                    shutterButton
                        .padding(.trailing, 18)
                }
            } else {
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
        .accessibilityLabel("Capture wigglegram")
        .accessibilityIdentifier("wigglecamCaptureButton")
    }

    // MARK: - Review (compact floating actions)

    private var reviewChrome: some View {
        VStack {
            Spacer()
            HStack(spacing: 12) {
                if let saveFlash {
                    Text(saveFlash)
                        .font(.caption.weight(.semibold))
                        .foregroundStyle(.white)
                        .padding(.horizontal, 12)
                        .padding(.vertical, 8)
                        .background(.black.opacity(0.55), in: Capsule())
                        .accessibilityIdentifier("wigglecamSaveFlash")
                    Spacer()
                } else if let saveError {
                    Text(saveError)
                        .font(.caption)
                        .foregroundStyle(.white)
                        .padding(.horizontal, 12)
                        .padding(.vertical, 8)
                        .background(.red.opacity(0.85), in: Capsule())
                        .accessibilityIdentifier("wigglecamSaveError")
                    Spacer()
                } else {
                    Spacer()
                }

                compactIconButton(
                    systemName: "arrow.counterclockwise",
                    label: "Retake",
                    id: "wigglecamRetakeButton"
                ) {
                    session.clearCapture()
                    saveFlash = nil
                    saveError = nil
                }

                compactIconButton(
                    systemName: isSavingGIF ? nil : "square.and.arrow.down",
                    label: "Save GIF to Photos",
                    id: "wigglecamSaveGIFButton",
                    busy: isSavingGIF
                ) {
                    saveGIFToPhotos()
                }
            }
            .padding(.horizontal, 16)
            .padding(.bottom, 20)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private func compactIconButton(
        systemName: String?,
        label: String,
        id: String,
        busy: Bool = false,
        action: @escaping () -> Void
    ) -> some View {
        Button(action: action) {
            ZStack {
                Circle()
                    .fill(.ultraThinMaterial)
                    .frame(width: 48, height: 48)
                    .overlay(Circle().strokeBorder(.white.opacity(0.35), lineWidth: 1))
                if busy {
                    ProgressView()
                        .tint(.white)
                } else if let systemName {
                    Image(systemName: systemName)
                        .font(.body.weight(.semibold))
                        .foregroundStyle(.white)
                }
            }
        }
        .buttonStyle(.plain)
        .disabled(busy)
        .accessibilityLabel(label)
        .accessibilityIdentifier(id)
    }

    private var readinessBanner: some View {
        let ready = session.readiness.canCapture
        return Text(ready ? "Landscape · Level" : session.readiness.blockingReason)
            .font(.subheadline.weight(.semibold))
            .padding(.horizontal, 14)
            .padding(.vertical, 8)
            .background(ready ? Color.green.opacity(0.85) : Color.orange.opacity(0.9), in: Capsule())
            .foregroundStyle(.white)
            .accessibilityIdentifier("wigglecamReadinessBanner")
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

    // MARK: - Save

    private func saveGIFToPhotos() {
        guard let pair = session.capturedPair, !isSavingGIF else { return }
        isSavingGIF = true
        saveFlash = nil
        saveError = nil
        let left = pair.left
        let right = pair.right
        Task {
            do {
                guard let data = WiggleGIFEncoder.makeWiggleGIF(left: left, right: right) else {
                    throw WiggleGIFEncoder.EncoderError.encodingFailed
                }
                try await WiggleGIFPhotoSaver.saveGIF(data)
                await MainActor.run {
                    isSavingGIF = false
                    saveFlash = "Saved to Photos"
                    session.setStatusMessage("GIF saved to Photos.")
                }
                try? await Task.sleep(nanoseconds: 2_000_000_000)
                await MainActor.run {
                    if saveFlash == "Saved to Photos" {
                        saveFlash = nil
                    }
                }
            } catch {
                await MainActor.run {
                    isSavingGIF = false
                    saveError = error.localizedDescription
                }
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
        default: return "Wigglecam"
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

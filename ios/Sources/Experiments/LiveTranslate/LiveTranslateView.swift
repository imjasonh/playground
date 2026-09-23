import SwiftUI

/// Full-bleed camera with translated text painted over the original glyphs.
struct LiveTranslateView: View {
    @StateObject private var session = LiveTranslateSession()

    var body: some View {
        GeometryReader { geo in
            let landscape = geo.size.width > geo.size.height
            ZStack {
                Color.black
                stage(size: geo.size)
                floatingChrome(landscape: landscape)
            }
            .frame(width: geo.size.width, height: geo.size.height)
        }
        .background(Color.black)
        .ignoresSafeArea()
        .navigationBarTitleDisplayMode(.inline)
        .toolbarBackground(.hidden, for: .navigationBar)
        .toolbarColorScheme(.dark, for: .navigationBar)
        .onAppear {
            session.refreshModelStatus()
            session.start()
        }
        .onDisappear { session.stop() }
    }

    // MARK: - Stage

    private func stage(size: CGSize) -> some View {
        let imageSize = session.previewImageSize == .zero
            ? size
            : session.previewImageSize

        return ZStack {
            if let image = session.previewImage {
                Image(uiImage: image)
                    .resizable()
                    .scaledToFill()
                    .frame(width: size.width, height: size.height)
                    .clipped()
                    .accessibilityIdentifier("liveTranslatePreview")

                overlayLayer(imageSize: imageSize, viewSize: size)
            } else {
                placeholder
                    .frame(width: size.width, height: size.height)
            }
        }
        .accessibilityElement(children: .contain)
    }

    private func overlayLayer(imageSize: CGSize, viewSize: CGSize) -> some View {
        let transform = LocalLensCoordinateMapper.ContentTransform.aspectFill(
            imageSize: imageSize,
            viewSize: viewSize
        )
        return ZStack {
            ForEach(session.overlays) { overlay in
                overlayCard(overlay, transform: transform)
            }
        }
        .allowsHitTesting(false)
        .accessibilityHidden(true)
    }

    private func overlayCard(
        _ overlay: LiveTranslateOverlay,
        transform: LocalLensCoordinateMapper.ContentTransform
    ) -> some View {
        let rect = transform.viewRect(
            imageRect: LocalLensCoordinateMapper.imageRect(
                fromVisionNormalized: overlay.boundingBox,
                imageSize: transform.imageSize
            )
        )
        let fill = Color(
            red: overlay.backdrop.red,
            green: overlay.backdrop.green,
            blue: overlay.backdrop.blue
        )
        let ink = overlay.backdrop.usesDarkText ? Color.black : Color.white
        let fontSize = LiveTranslateResultBuilder.fittedFontSize(
            text: overlay.displayText,
            box: rect.size
        )

        return ZStack {
            if overlay.isTranslated {
                RoundedRectangle(cornerRadius: 3, style: .continuous)
                    .fill(fill.opacity(0.94))
                Text(overlay.displayText)
                    .font(.system(size: fontSize, weight: .semibold))
                    .foregroundStyle(ink)
                    .multilineTextAlignment(.center)
                    .minimumScaleFactor(0.5)
                    .lineLimit(4)
                    .padding(.horizontal, 4)
                    .padding(.vertical, 2)
            } else {
                RoundedRectangle(cornerRadius: 3, style: .continuous)
                    .stroke(Color.white.opacity(0.85), lineWidth: 1.5)
            }
        }
        .frame(width: max(rect.width, 8), height: max(rect.height, 8))
        .position(x: rect.midX, y: rect.midY)
    }

    // MARK: - Floating chrome

    private func floatingChrome(landscape: Bool) -> some View {
        ZStack {
            VStack(spacing: 0) {
                topBar
                    .padding(.top, 52)
                    .padding(.horizontal, 12)

                Spacer(minLength: 0)

                if !landscape {
                    bottomBar
                        .padding(.horizontal, 10)
                        .padding(.bottom, 18)
                }
            }

            if landscape {
                HStack(spacing: 0) {
                    Spacer(minLength: 0)
                    trailingRail
                        .padding(.trailing, 10)
                        .padding(.bottom, 14)
                }
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var topBar: some View {
        HStack(spacing: 8) {
            Text(session.statusMessage)
                .font(.caption.weight(.medium))
                .foregroundStyle(.white)
                .lineLimit(2)
                .padding(.horizontal, 10)
                .padding(.vertical, 6)
                .background(.black.opacity(0.45), in: Capsule())
                .accessibilityIdentifier("liveTranslateStatusMessage")

            Spacer(minLength: 8)

            modelBadge
        }
    }

    private var modelBadge: some View {
        Image(systemName: session.modelGate.isAvailable ? "checkmark.circle.fill" : "sparkles")
            .font(.caption.weight(.semibold))
            .foregroundStyle(session.modelGate.isAvailable ? Color.green : Color.orange)
            .padding(8)
            .background(.black.opacity(0.4), in: Circle())
            .frame(minWidth: 44, minHeight: 44)
            .contentShape(Rectangle())
            .accessibilityIdentifier("liveTranslateModelBadge")
            .accessibilityLabel(modelBadgeLabel)
    }

    private var modelBadgeLabel: String {
        switch session.modelGate {
        case .available:
            return "On-device model ready"
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence"
        case .modelNotReady:
            return "Model still downloading"
        case .deviceNotEligible:
            return "Device not eligible"
        case .other:
            return "Apple Intelligence unavailable"
        }
    }

    private var bottomBar: some View {
        HStack(spacing: 8) {
            languageMenu
            copyButton
            flipCameraButton
        }
        .padding(8)
        .background(.black.opacity(0.4), in: Capsule())
    }

    private var trailingRail: some View {
        VStack(spacing: 8) {
            languageMenu
            copyButton
            flipCameraButton
        }
        .padding(8)
        .background(.black.opacity(0.4), in: RoundedRectangle(cornerRadius: 22, style: .continuous))
    }

    private var languageMenu: some View {
        Menu {
            ForEach(LiveTranslateLanguage.allCases) { language in
                Button {
                    session.setLanguage(language)
                } label: {
                    if language == session.language {
                        Label(language.displayName, systemImage: "checkmark")
                    } else {
                        Text(language.displayName)
                    }
                }
                .accessibilityIdentifier("liveTranslateLanguage-\(language.rawValue)")
            }
        } label: {
            Image(systemName: "globe")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(width: 36, height: 36)
                .background(Color.white.opacity(0.18), in: Circle())
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .accessibilityIdentifier("liveTranslateLanguageButton")
        .accessibilityLabel("Translate to \(session.language.displayName)")
    }

    private var copyButton: some View {
        Button {
            session.copyToClipboard()
        } label: {
            Image(systemName: session.didCopy ? "checkmark" : "doc.on.doc")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(width: 36, height: 36)
                .background(
                    session.canCopy ? Color.white.opacity(0.18) : Color.white.opacity(0.08),
                    in: Circle()
                )
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .disabled(!session.canCopy)
        .accessibilityIdentifier("liveTranslateCopyButton")
        .accessibilityLabel(session.didCopy ? "Copied" : "Copy translation")
    }

    private var flipCameraButton: some View {
        Button {
            session.flipCamera()
        } label: {
            Image(systemName: "arrow.triangle.2.circlepath.camera")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(width: 36, height: 36)
                .background(
                    session.runState == .running
                        ? Color.white.opacity(0.18)
                        : Color.white.opacity(0.08),
                    in: Circle()
                )
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .disabled(session.runState != .running)
        .accessibilityIdentifier("liveTranslateFlipCameraButton")
        .accessibilityLabel(
            session.usingFrontCamera ? "Switch to rear camera" : "Switch to front camera"
        )
    }

    private var placeholder: some View {
        VStack(spacing: 12) {
            Image(systemName: placeholderSymbol)
                .font(.largeTitle)
                .foregroundStyle(.white.opacity(0.85))
                .accessibilityHidden(true)
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
                    Color(red: 0.07, green: 0.09, blue: 0.14),
                    Color(red: 0.02, green: 0.03, blue: 0.05),
                ],
                startPoint: .topLeading,
                endPoint: .bottomTrailing
            )
        )
        .accessibilityIdentifier("liveTranslatePlaceholder")
    }

    private var placeholderSymbol: String {
        switch session.runState {
        case .permissionDenied:
            return "lock.slash"
        case .noCamera, .failed:
            return "camera.badge.ellipsis"
        case .requestingPermission:
            return "camera"
        default:
            return "translate"
        }
    }

    private var placeholderTitle: String {
        switch session.runState {
        case .permissionDenied:
            return "Camera locked"
        case .noCamera:
            return "No camera"
        case .failed:
            return "Couldn't start"
        case .requestingPermission:
            return "Starting…"
        case .running:
            return "Waiting for frames…"
        case .idle:
            return "Live Translate"
        }
    }
}

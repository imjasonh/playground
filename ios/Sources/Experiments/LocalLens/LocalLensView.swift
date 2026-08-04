import SwiftUI

/// Local Lens — live camera labels from on-device Vision (no network).
struct LocalLensView: View {
    @StateObject private var session = LocalLensSession()

    var body: some View {
        VStack(spacing: 0) {
            preview
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .background(Color.black)

            controls
                .padding()
                .background(.ultraThinMaterial)
        }
        .onAppear { session.start() }
        .onDisappear { session.stop() }
    }

    private var preview: some View {
        GeometryReader { geo in
            ZStack {
                if let image = session.previewImage {
                    Image(uiImage: image)
                        .resizable()
                        .scaledToFill()
                        .frame(width: geo.size.width, height: geo.size.height)
                        .clipped()
                        .accessibilityIdentifier("localLensPreview")

                    boxesOverlay(size: geo.size)
                    chipsOverlay
                } else {
                    placeholder
                        .frame(width: geo.size.width, height: geo.size.height)
                }
            }
        }
        .accessibilityElement(children: .contain)
    }

    private var chipsOverlay: some View {
        VStack {
            Spacer()
            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    ForEach(session.result.findings) { finding in
                        Text(LocalLensResultBuilder.chipText(for: finding))
                            .font(.caption.weight(.semibold))
                            .padding(.horizontal, 10)
                            .padding(.vertical, 6)
                            .background(.black.opacity(0.55), in: Capsule())
                            .foregroundStyle(.white)
                    }
                }
                .padding(.horizontal, 12)
                .padding(.bottom, 12)
            }
            .accessibilityIdentifier("localLensFindingsChips")
        }
    }

    private func boxesOverlay(size: CGSize) -> some View {
        Canvas { context, _ in
            for finding in session.result.findings {
                guard let box = finding.boundingBox else { continue }
                // Vision: origin bottom-left → SwiftUI: origin top-left.
                let rect = CGRect(
                    x: box.origin.x * size.width,
                    y: (1 - box.origin.y - box.height) * size.height,
                    width: box.width * size.width,
                    height: box.height * size.height
                )
                let path = Path(roundedRect: rect, cornerRadius: 6)
                context.stroke(path, with: .color(.green.opacity(0.9)), lineWidth: 2)
            }
        }
        .allowsHitTesting(false)
        .accessibilityHidden(true)
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
                    Color(red: 0.06, green: 0.1, blue: 0.12),
                    Color(red: 0.02, green: 0.03, blue: 0.05),
                ],
                startPoint: .topLeading,
                endPoint: .bottomTrailing
            )
        )
    }

    private var controls: some View {
        VStack(alignment: .leading, spacing: 14) {
            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("localLensStatusMessage")

            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    ForEach(LocalLensMode.allCases) { mode in
                        modeButton(mode)
                    }
                }
            }
            .accessibilityIdentifier("localLensModePicker")

            HStack {
                Button {
                    session.flipCamera()
                } label: {
                    Label(
                        session.usingFrontCamera ? "Front" : "Rear",
                        systemImage: "arrow.triangle.2.circlepath.camera"
                    )
                }
                .buttonStyle(.bordered)
                .disabled(session.runState != .running)
                .accessibilityIdentifier("localLensFlipCameraButton")

                Spacer()

                Label("On-device only", systemImage: "lock.iphone")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("localLensPrivacyBadge")
            }

            Text("Uses Apple’s Vision framework entirely on-device — classify scenes, read text, find animals/faces/people, and scan barcodes. Frames are never uploaded.")
                .font(.caption2)
                .foregroundStyle(.tertiary)
        }
    }

    private func modeButton(_ mode: LocalLensMode) -> some View {
        let selected = session.mode == mode
        return Button {
            session.setMode(mode)
        } label: {
            Label(mode.title, systemImage: mode.symbolName)
                .font(.subheadline.weight(.semibold))
                .padding(.horizontal, 12)
                .padding(.vertical, 8)
                .background(selected ? Color.accentColor.opacity(0.2) : Color.secondary.opacity(0.12), in: Capsule())
                .foregroundStyle(selected ? Color.accentColor : Color.primary)
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier("localLensMode-\(mode.rawValue)")
        .accessibilityAddTraits(selected ? [.isSelected] : [])
        .accessibilityLabel(mode.title)
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
            return "camera.viewfinder"
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
            return "Local Lens"
        }
    }
}

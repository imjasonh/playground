import SwiftUI

/// Local Lens — full-bleed camera with compact floating Vision controls.
struct LocalLensView: View {
    @StateObject private var session = LocalLensSession()

    var body: some View {
        GeometryReader { geo in
            let landscape = geo.size.width > geo.size.height
            ZStack {
                Color.black
                stage(size: geo.size)
                floatingChrome(landscape: landscape, size: geo.size)
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

    // MARK: - Stage

    private func stage(size: CGSize) -> some View {
        ZStack {
            if let image = session.previewImage {
                Image(uiImage: image)
                    .resizable()
                    .scaledToFill()
                    .frame(width: size.width, height: size.height)
                    .clipped()
                    .accessibilityIdentifier("localLensPreview")

                geometryOverlay(size: size)
            } else {
                placeholder
                    .frame(width: size.width, height: size.height)
            }
        }
        .accessibilityElement(children: .contain)
    }

    private func floatingChrome(landscape: Bool, size: CGSize) -> some View {
        ZStack {
            VStack(spacing: 0) {
                topBar
                    .padding(.top, 52)
                    .padding(.horizontal, 12)

                Spacer(minLength: 0)

                if !landscape {
                    findingsChips
                        .padding(.bottom, 8)
                    bottomBar
                        .padding(.horizontal, 10)
                        .padding(.bottom, 18)
                }
            }

            if landscape {
                HStack(spacing: 0) {
                    Spacer(minLength: 0)
                    VStack(spacing: 10) {
                        Spacer(minLength: 0)
                        findingsChips
                            .frame(maxWidth: min(size.width * 0.42, 280), alignment: .trailing)
                        trailingRail
                    }
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
                .accessibilityIdentifier("localLensStatusMessage")

            Spacer(minLength: 8)

            Label("On-device", systemImage: "lock.iphone")
                .font(.caption2.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
                .padding(.horizontal, 8)
                .padding(.vertical, 6)
                .background(.black.opacity(0.4), in: Capsule())
                .labelStyle(.titleAndIcon)
                .accessibilityIdentifier("localLensPrivacyBadge")
        }
    }

    private var bottomBar: some View {
        HStack(spacing: 8) {
            modePicker(axis: .horizontal)
            flipCameraButton
        }
        .padding(8)
        .background(.black.opacity(0.4), in: Capsule())
    }

    private var trailingRail: some View {
        VStack(spacing: 8) {
            modePicker(axis: .vertical)
            flipCameraButton
        }
        .padding(8)
        .background(.black.opacity(0.4), in: RoundedRectangle(cornerRadius: 22, style: .continuous))
    }

    private enum PickerAxis {
        case horizontal
        case vertical
    }

    private func modePicker(axis: PickerAxis) -> some View {
        let modes = LocalLensMode.allCases
        return Group {
            switch axis {
            case .horizontal:
                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 6) {
                        ForEach(modes) { mode in
                            modeButton(mode)
                        }
                    }
                }
            case .vertical:
                ScrollView(.vertical, showsIndicators: false) {
                    VStack(spacing: 6) {
                        ForEach(modes) { mode in
                            modeButton(mode)
                        }
                    }
                }
                .frame(maxHeight: 280)
            }
        }
        .accessibilityIdentifier("localLensModePicker")
    }

    private var findingsChips: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 6) {
                ForEach(session.result.findings.prefix(4)) { finding in
                    Text(LocalLensResultBuilder.chipText(for: finding))
                        .font(.caption2.weight(.semibold))
                        .padding(.horizontal, 8)
                        .padding(.vertical, 4)
                        .background(.black.opacity(0.5), in: Capsule())
                        .foregroundStyle(.white)
                }
            }
            .padding(.horizontal, 10)
        }
        .accessibilityIdentifier("localLensFindingsChips")
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
        }
        .buttonStyle(.plain)
        .disabled(session.runState != .running)
        .accessibilityIdentifier("localLensFlipCameraButton")
        .accessibilityLabel(session.usingFrontCamera ? "Front camera" : "Rear camera")
        .accessibilityHint("Flip camera")
    }

    private func modeButton(_ mode: LocalLensMode) -> some View {
        let selected = session.mode == mode
        return Button {
            session.setMode(mode)
        } label: {
            Image(systemName: mode.symbolName)
                .font(.footnote.weight(.semibold))
                .foregroundStyle(selected ? .black : .white)
                .frame(width: 34, height: 34)
                .background(
                    selected ? Color.white.opacity(0.95) : Color.white.opacity(0.14),
                    in: Circle()
                )
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier("localLensMode-\(mode.rawValue)")
        .accessibilityAddTraits(selected ? [.isSelected] : [])
        .accessibilityLabel(mode.title)
    }

    // MARK: - Overlays

    private func geometryOverlay(size: CGSize) -> some View {
        Canvas { context, _ in
            let result = session.result

            for finding in result.findings {
                guard let box = finding.boundingBox else { continue }
                let rect = Self.viewRect(for: box, in: size)
                let path = Path(roundedRect: rect, cornerRadius: 6)
                context.stroke(path, with: .color(.green.opacity(0.85)), lineWidth: 2)
            }

            for bone in result.bones {
                var path = Path()
                path.move(to: Self.viewPoint(for: bone.from, in: size))
                path.addLine(to: Self.viewPoint(for: bone.to, in: size))
                context.stroke(path, with: .color(.cyan.opacity(0.95)), lineWidth: 2.5)
            }

            for joint in result.joints {
                let center = Self.viewPoint(for: joint, in: size)
                let dot = Path(ellipseIn: CGRect(x: center.x - 3.5, y: center.y - 3.5, width: 7, height: 7))
                context.fill(dot, with: .color(.yellow.opacity(0.95)))
            }
        }
        .allowsHitTesting(false)
        .accessibilityHidden(true)
    }

    /// Vision-normalized point (origin bottom-left) → view point (origin top-left).
    private static func viewPoint(for normalized: CGPoint, in size: CGSize) -> CGPoint {
        CGPoint(x: normalized.x * size.width, y: (1 - normalized.y) * size.height)
    }

    private static func viewRect(for box: CGRect, in size: CGSize) -> CGRect {
        CGRect(
            x: box.origin.x * size.width,
            y: (1 - box.origin.y - box.height) * size.height,
            width: box.width * size.width,
            height: box.height * size.height
        )
    }

    private var placeholder: some View {
        VStack(spacing: 12) {
            Image(systemName: placeholderSymbol)
                .font(.system(size: 44))
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

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
                floatingChrome(landscape: landscape)
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
                    .accessibilityIdentifier("localLensPreview")

                detectionOverlay(imageSize: imageSize, viewSize: size)
            } else {
                placeholder
                    .frame(width: size.width, height: size.height)
            }
        }
        .accessibilityElement(children: .contain)
    }

    /// Boxes with labels + pose skeleton, mapped through aspect-fill into the view.
    private func detectionOverlay(imageSize: CGSize, viewSize: CGSize) -> some View {
        let transform = LocalLensCoordinateMapper.ContentTransform.aspectFill(
            imageSize: imageSize,
            viewSize: viewSize
        )
        let boxedFindings = session.result.findings.filter { $0.boundingBox != nil }

        return ZStack {
            Canvas { context, _ in
                for bone in session.result.bones {
                    var path = Path()
                    path.move(
                        to: transform.viewPoint(
                            imagePoint: LocalLensCoordinateMapper.imagePoint(
                                fromVisionNormalized: bone.from,
                                imageSize: transform.imageSize
                            )
                        )
                    )
                    path.addLine(
                        to: transform.viewPoint(
                            imagePoint: LocalLensCoordinateMapper.imagePoint(
                                fromVisionNormalized: bone.to,
                                imageSize: transform.imageSize
                            )
                        )
                    )
                    context.stroke(path, with: .color(.cyan.opacity(0.95)), lineWidth: 2.5)
                }

                for joint in session.result.joints {
                    let center = transform.viewPoint(
                        imagePoint: LocalLensCoordinateMapper.imagePoint(
                            fromVisionNormalized: joint,
                            imageSize: transform.imageSize
                        )
                    )
                    let dot = Path(ellipseIn: CGRect(x: center.x - 3.5, y: center.y - 3.5, width: 7, height: 7))
                    context.fill(dot, with: .color(.yellow.opacity(0.95)))
                }

                for finding in boxedFindings {
                    guard let box = finding.boundingBox else { continue }
                    let rect = transform.viewRect(
                        imageRect: LocalLensCoordinateMapper.imageRect(
                            fromVisionNormalized: box,
                            imageSize: transform.imageSize
                        )
                    )
                    let path = Path(roundedRect: rect, cornerRadius: 5)
                    context.stroke(path, with: .color(.green.opacity(0.9)), lineWidth: 2)
                }
            }

            ForEach(boxedFindings) { finding in
                overlayLabel(for: finding, transform: transform, viewSize: viewSize)
            }
        }
        .allowsHitTesting(false)
        .accessibilityHidden(true)
    }

    @ViewBuilder
    private func overlayLabel(
        for finding: LocalLensFinding,
        transform: LocalLensCoordinateMapper.ContentTransform,
        viewSize: CGSize
    ) -> some View {
        if let box = finding.boundingBox {
            overlayLabelContent(
                text: LocalLensResultBuilder.chipText(for: finding),
                rect: transform.viewRect(
                    imageRect: LocalLensCoordinateMapper.imageRect(
                        fromVisionNormalized: box,
                        imageSize: transform.imageSize
                    )
                ),
                viewSize: viewSize
            )
        }
    }

    private func overlayLabelContent(text: String, rect: CGRect, viewSize: CGSize) -> some View {
        // Prefer above the box; flip below when near the top edge.
        let labelAbove = rect.minY > 28
        let y = labelAbove ? max(rect.minY - 12, 10) : min(rect.minY + 14, viewSize.height - 10)
        return Text(text)
            .font(.caption2.weight(.bold))
            .foregroundStyle(.white)
            .padding(.horizontal, 6)
            .padding(.vertical, 3)
            .background(Color.green.opacity(0.85), in: Capsule())
            .position(
                x: min(max(rect.midX, 40), viewSize.width - 40),
                y: y
            )
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
                    // Classify has no boxes — keep chips; otherwise labels sit on the detections.
                    if session.result.findings.contains(where: { $0.boundingBox == nil }) {
                        findingsChips
                            .padding(.bottom, 8)
                    }
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
                        if session.result.findings.contains(where: { $0.boundingBox == nil }) {
                            findingsChips
                                .frame(maxWidth: 260, alignment: .trailing)
                        }
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
                .lineLimit(1)
                .padding(.horizontal, 10)
                .padding(.vertical, 6)
                .background(.black.opacity(0.45), in: Capsule())
                .accessibilityIdentifier("localLensStatusMessage")

            Spacer(minLength: 8)

            Image(systemName: "lock.iphone")
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
                .padding(8)
                .background(.black.opacity(0.4), in: Circle())
                .accessibilityIdentifier("localLensPrivacyBadge")
                .accessibilityLabel("On-device only")
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
                .frame(maxHeight: 260)
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

import SwiftUI

/// Full-bleed camera with dye swatches. The tint is applied to hair pixels only.
struct HairColorView: View {
    @StateObject private var session = HairColorSession()

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

    private func stage(size: CGSize) -> some View {
        ZStack {
            if let image = session.stillImage ?? session.previewImage {
                Image(uiImage: image)
                    .resizable()
                    .scaledToFill()
                    .frame(width: size.width, height: size.height)
                    .clipped()
                    .accessibilityIdentifier("hairColorPreview")
                    .accessibilityLabel(session.stillImage == nil ? "Camera preview" : "Tinted photo")
            } else {
                placeholder
                    .frame(width: size.width, height: size.height)
            }
        }
    }

    private func floatingChrome(landscape: Bool) -> some View {
        ZStack {
            VStack(spacing: 0) {
                topBar
                    .padding(.top, 52)
                    .padding(.horizontal, 12)
                Spacer(minLength: 0)
                if !landscape, session.runState == .running {
                    controls(maxWidth: .infinity)
                        .padding(.horizontal, 12)
                        .padding(.bottom, 18)
                }
            }
            if landscape, session.runState == .running {
                HStack {
                    Spacer(minLength: 0)
                    controls(maxWidth: 280)
                        .padding(.trailing, 12)
                        .padding(.bottom, 14)
                }
            }
        }
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
                .accessibilityIdentifier("hairColorStatusMessage")

            Spacer(minLength: 8)

            Image(systemName: "lock.iphone")
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white.opacity(0.9))
                .padding(8)
                .background(.black.opacity(0.4), in: Circle())
                .accessibilityLabel("On-device only")
        }
    }

    private func controls(maxWidth: CGFloat) -> some View {
        VStack(alignment: .leading, spacing: 8) {
            if session.stillImage == nil {
                dyePicker
                strengthRow
            }
            buttonRow
        }
        .padding(10)
        .frame(maxWidth: maxWidth, alignment: .leading)
        .background(.black.opacity(0.4), in: RoundedRectangle(cornerRadius: 22, style: .continuous))
    }

    private var dyePicker: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 4) {
                ForEach(HairDye.all) { dye in
                    dyeButton(dye)
                }
            }
        }
        .accessibilityIdentifier("hairColorDyePicker")
    }

    private func dyeButton(_ dye: HairDye) -> some View {
        let selected = session.dye == dye
        return Button {
            session.setDye(dye)
        } label: {
            ZStack {
                Circle()
                    .fill(dye.color)
                    .frame(width: 28, height: 28)
                    .overlay {
                        Circle()
                            .strokeBorder(Color.white.opacity(selected ? 0.95 : 0.25), lineWidth: selected ? 2 : 1)
                    }
                if selected {
                    Image(systemName: "checkmark")
                        .font(.caption2.weight(.bold))
                        .foregroundStyle(dye.prefersDarkCheckmark ? Color.black : Color.white)
                        .accessibilityHidden(true)
                }
            }
            .frame(minWidth: 44, minHeight: 44)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier("hairColorDye-\(dye.id)")
        .accessibilityLabel(dye.name)
        .accessibilityAddTraits(selected ? [.isSelected] : [])
    }

    private var strengthRow: some View {
        HStack(spacing: 8) {
            Text("Strength")
                .font(.caption.weight(.semibold))
                .foregroundStyle(.white)
                .accessibilityHidden(true)
            Slider(
                value: Binding(
                    get: { session.strength },
                    set: { session.setStrength($0) }
                ),
                in: 0...1
            )
            .tint(.white)
            .accessibilityIdentifier("hairColorStrengthSlider")
            .accessibilityLabel("Color strength")
            .accessibilityValue(Text("\(strengthPercent) percent"))
            Text("\(strengthPercent)%")
                .font(.caption.monospacedDigit())
                .foregroundStyle(.white)
                .frame(minWidth: 36, alignment: .trailing)
                .accessibilityHidden(true)
        }
    }

    private var strengthPercent: Int {
        Int((session.strength * 100).rounded())
    }

    private var buttonRow: some View {
        HStack(spacing: 8) {
            if session.stillImage == nil {
                maskButton
                Spacer(minLength: 0)
                if session.canCapture {
                    captureButton
                }
                flipCameraButton
            } else {
                Spacer(minLength: 0)
                retakeButton
                Spacer(minLength: 0)
            }
        }
    }

    private var maskButton: some View {
        Button {
            session.setShowsMask(!session.showsMask)
        } label: {
            Image(systemName: session.showsMask ? "eye.slash" : "eye")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier("hairColorMaskButton")
        .accessibilityLabel(session.showsMask ? "Hide hair mask" : "Show hair mask")
        .accessibilityAddTraits(session.showsMask ? [.isSelected] : [])
    }

    private var captureButton: some View {
        Button {
            session.capture()
        } label: {
            Image(systemName: "camera.circle.fill")
                .font(.largeTitle)
                .foregroundStyle(.white)
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .disabled(session.isCapturing)
        .accessibilityIdentifier("hairColorCaptureButton")
        .accessibilityLabel("Take photo")
    }

    private var flipCameraButton: some View {
        Button {
            session.flipCamera()
        } label: {
            Image(systemName: "arrow.triangle.2.circlepath.camera")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(minWidth: 44, minHeight: 44)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .disabled(session.runState != .running)
        .accessibilityIdentifier("hairColorFlipCameraButton")
        .accessibilityLabel(
            session.usingFrontCamera ? "Switch to rear camera" : "Switch to front camera"
        )
    }

    private var retakeButton: some View {
        Button {
            session.retake()
        } label: {
            Text("Retake")
                .font(.body.weight(.semibold))
                .foregroundStyle(.black)
                .padding(.horizontal, 18)
                .frame(minHeight: 44)
                .background(Color.white, in: Capsule())
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier("hairColorRetakeButton")
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
                    Color(red: 0.08, green: 0.06, blue: 0.10),
                    Color(red: 0.02, green: 0.02, blue: 0.04),
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
            return "paintpalette.fill"
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
            return "Hair Color"
        }
    }
}

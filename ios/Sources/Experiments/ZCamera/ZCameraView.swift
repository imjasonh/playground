import SwiftUI

/// Z-Camera — live preview where only a chosen depth band stays visible.
struct ZCameraView: View {
    @StateObject private var session = ZCameraSession()
    @State private var nearSlider = ZDepthSliderMapping.sliderValue(for: .meters(0))
    @State private var farSlider = ZDepthSliderMapping.sliderValue(for: .infinity)

    var body: some View {
        VStack(spacing: 0) {
            preview
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .background(Color.black)

            controls
                .padding()
                .background(.ultraThinMaterial)
        }
        .onAppear {
            publishBand()
            session.start()
        }
        .onDisappear { session.stop() }
        .onChange(of: nearSlider) { _ in publishBand() }
        .onChange(of: farSlider) { _ in publishBand() }
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
                        .accessibilityIdentifier("zCameraPreview")
                } else {
                    placeholder
                        .frame(width: geo.size.width, height: geo.size.height)
                }
            }
        }
        .accessibilityElement(children: .contain)
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
                    Color(red: 0.05, green: 0.08, blue: 0.14),
                    Color(red: 0.02, green: 0.02, blue: 0.05),
                ],
                startPoint: .topLeading,
                endPoint: .bottomTrailing
            )
        )
    }

    private var controls: some View {
        VStack(alignment: .leading, spacing: 16) {
            Text(session.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("zCameraStatusMessage")

            bandSlider(
                title: "Near",
                value: $nearSlider,
                accessibilityID: "zCameraNearSlider"
            )
            bandSlider(
                title: "Far",
                value: $farSlider,
                accessibilityID: "zCameraFarSlider"
            )

            HStack {
                Label(session.usingFrontCamera ? "Front depth" : "Rear depth", systemImage: "camera.metering.matrix")
                Spacer()
                Text(bandSummary)
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("zCameraBandSummary")
            }
            .font(.caption)
            .foregroundStyle(.secondary)

            Text("Pixels closer than Near or farther than Far go black. Drag either end to 0 or ∞.")
                .font(.caption2)
                .foregroundStyle(.tertiary)
        }
    }

    private func bandSlider(title: String, value: Binding<Double>, accessibilityID: String) -> some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text(title)
                    .font(.subheadline.weight(.semibold))
                Spacer()
                Text(ZDepthBand.Bound.label(ZDepthSliderMapping.bound(sliderValue: value.wrappedValue)))
                    .font(.subheadline.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("\(accessibilityID)Label")
            }
            Slider(value: value, in: 0...1)
                .accessibilityIdentifier(accessibilityID)
                .accessibilityLabel(title)
                .accessibilityValue(ZDepthBand.Bound.label(ZDepthSliderMapping.bound(sliderValue: value.wrappedValue)))
        }
    }

    private var bandSummary: String {
        let near = ZDepthBand.Bound.label(session.band.near)
        let far = ZDepthBand.Bound.label(session.band.far)
        return "\(near) – \(far)"
    }

    private var placeholderSymbol: String {
        switch session.runState {
        case .permissionDenied:
            return "lock.slash"
        case .noDepthCamera, .failed:
            return "camera.metering.unknown"
        case .requestingPermission:
            return "camera"
        default:
            return "square.3.layers.3d.down.right"
        }
    }

    private var placeholderTitle: String {
        switch session.runState {
        case .permissionDenied:
            return "Camera locked"
        case .noDepthCamera:
            return "No depth camera"
        case .failed:
            return "Couldn't start"
        case .requestingPermission:
            return "Starting…"
        case .running:
            return "Waiting for frames…"
        case .idle:
            return "Z-Camera"
        }
    }

    private func publishBand() {
        // Keep the interval ordered while dragging either thumb.
        if nearSlider > farSlider {
            if nearSlider != ZDepthSliderMapping.sliderValue(for: session.band.near) {
                farSlider = nearSlider
            } else {
                nearSlider = farSlider
            }
        }
        session.updateBand(
            ZDepthBand(
                near: ZDepthSliderMapping.bound(sliderValue: nearSlider),
                far: ZDepthSliderMapping.bound(sliderValue: farSlider)
            )
        )
    }
}

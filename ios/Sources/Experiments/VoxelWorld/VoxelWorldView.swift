import ARKit
import SceneKit
import SwiftUI

/// Voxel World — ARKit rebuilds the room as colored voxels.
struct VoxelWorldView: View {
    @StateObject private var session = VoxelWorldSession()
    @State private var sizeSlider = VoxelSizeMapping.sliderValue(for: VoxelSizeMapping.defaultSize)
    @State private var frozen = false
    @State private var showCameraFeed = true

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
            session.updateFrozen(frozen)
            session.updateShowsCameraFeed(showCameraFeed)
            session.start()
        }
        .onDisappear { session.stop() }
        .onChange(of: frozen) { session.updateFrozen($0) }
        .onChange(of: showCameraFeed) { session.updateShowsCameraFeed($0) }
    }

    private var preview: some View {
        GeometryReader { geo in
            ZStack {
                if showsARView {
                    VoxelARViewContainer(view: session.arView)
                        .frame(width: geo.size.width, height: geo.size.height)
                        .accessibilityIdentifier("voxelWorldPreview")
                } else {
                    placeholder
                        .frame(width: geo.size.width, height: geo.size.height)
                }
            }
        }
        .accessibilityElement(children: .contain)
    }

    private var showsARView: Bool {
        switch session.runState {
        case .running, .requestingPermission, .idle:
            return true
        case .unsupported, .permissionDenied, .failed:
            return false
        }
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
                    Color(red: 0.06, green: 0.05, blue: 0.12),
                    Color(red: 0.02, green: 0.02, blue: 0.05),
                ],
                startPoint: .topLeading,
                endPoint: .bottomTrailing
            )
        )
    }

    private var controls: some View {
        VStack(alignment: .leading, spacing: 16) {
            HStack {
                Text(session.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("voxelStatusMessage")
                Text("\(session.voxelCount)")
                    .font(.footnote.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("voxelCountLabel")
            }

            VStack(alignment: .leading, spacing: 6) {
                HStack {
                    Text("Voxel size")
                        .font(.subheadline.weight(.semibold))
                    Spacer()
                    Text(VoxelSizeMapping.label(for: VoxelSizeMapping.size(sliderValue: sizeSlider)))
                        .font(.subheadline.monospacedDigit())
                        .foregroundStyle(.secondary)
                        .accessibilityIdentifier("voxelSizeLabel")
                }
                Slider(value: $sizeSlider, in: 0...1) { editing in
                    // Rebuilding the grid clears it, so only apply once the
                    // drag ends instead of on every tick.
                    if !editing {
                        session.updateVoxelSize(VoxelSizeMapping.size(sliderValue: sizeSlider))
                    }
                }
                .accessibilityIdentifier("voxelSizeSlider")
                .accessibilityLabel("Voxel size")
                .accessibilityValue(VoxelSizeMapping.label(for: VoxelSizeMapping.size(sliderValue: sizeSlider)))
            }

            HStack(spacing: 12) {
                checkbox(
                    "Freeze",
                    isOn: $frozen,
                    accessibilityID: "voxelFreezeCheckbox"
                )
                checkbox(
                    "Camera feed",
                    isOn: $showCameraFeed,
                    accessibilityID: "voxelCameraFeedCheckbox"
                )
                Spacer()
                Button(role: .destructive) {
                    session.resetVoxels()
                } label: {
                    Label("Reset", systemImage: "trash")
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("voxelResetButton")
            }
            .font(.subheadline)

            Text("Voxels are colored from the camera pixel that saw that point in space. Changing the voxel size clears the world; Freeze stops scanning so you can walk around what you built. Best with LiDAR (iPhone/iPad Pro); without it, sparse tracked feature points are voxelized instead.")
                .font(.caption2)
                .foregroundStyle(.tertiary)
        }
    }

    private func checkbox(_ title: String, isOn: Binding<Bool>, accessibilityID: String) -> some View {
        Button {
            isOn.wrappedValue.toggle()
        } label: {
            Label(
                title,
                systemImage: isOn.wrappedValue ? "checkmark.square.fill" : "square"
            )
        }
        .buttonStyle(.plain)
        .accessibilityIdentifier(accessibilityID)
        .accessibilityAddTraits(isOn.wrappedValue ? [.isSelected] : [])
        .accessibilityLabel(title)
        .accessibilityValue(isOn.wrappedValue ? "On" : "Off")
    }

    private var placeholderSymbol: String {
        switch session.runState {
        case .permissionDenied:
            return "lock.slash"
        case .unsupported, .failed:
            return "arkit"
        default:
            return "cube.transparent"
        }
    }

    private var placeholderTitle: String {
        switch session.runState {
        case .permissionDenied:
            return "Camera locked"
        case .unsupported:
            return "ARKit unavailable"
        case .failed:
            return "Couldn't start"
        case .requestingPermission:
            return "Starting…"
        case .running:
            return "Waiting for frames…"
        case .idle:
            return "Voxel World"
        }
    }
}

/// Hosts the session-owned `ARSCNView` in SwiftUI.
private struct VoxelARViewContainer: UIViewRepresentable {
    let view: ARSCNView

    func makeUIView(context: Context) -> ARSCNView { view }
    func updateUIView(_ uiView: ARSCNView, context: Context) {}
}

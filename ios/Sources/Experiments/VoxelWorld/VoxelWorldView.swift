import ARKit
import SceneKit
import SwiftUI

/// Voxel World. ARKit rebuilds the room as colored voxels.
struct VoxelWorldView: View {
    @StateObject private var session = VoxelWorldSession()

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
        VStack(spacing: 12) {
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

            HStack {
                Spacer()
                Button {
                    session.saveCurrentFrame()
                } label: {
                    Image(systemName: "camera.fill")
                        .font(.title2)
                        .frame(minWidth: 44, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .buttonBorderShape(.circle)
                .disabled(session.isSavingPhoto)
                .accessibilityLabel("Take picture")
                .accessibilityIdentifier("voxelCaptureButton")
                Spacer()
            }
        }
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

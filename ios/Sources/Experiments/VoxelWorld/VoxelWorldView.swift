import ARKit
import SceneKit
import SwiftUI

/// Voxel Eyes. The voxel viewer fills the screen. Back and capture float on it.
struct VoxelWorldView: View {
    @Environment(\.dismiss) private var dismiss
    @StateObject private var session = VoxelWorldSession()

    var body: some View {
        ZStack {
            stage
                .ignoresSafeArea()
            floatingChrome
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .background(Color.black.ignoresSafeArea())
        .preferredColorScheme(.dark)
        .toolbar(.hidden, for: .navigationBar)
        .navigationBarBackButtonHidden(true)
        .onAppear { session.start() }
        .onDisappear { session.stop() }
    }

    private var stage: some View {
        ZStack {
            if showsARView {
                VoxelARViewContainer(view: session.arView)
                    .accessibilityIdentifier("voxelWorldPreview")
            } else {
                placeholder
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
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
        .padding(.bottom, 72)
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

    private var floatingChrome: some View {
        VStack {
            HStack {
                backButton
                Spacer()
            }
            Spacer()
            captureButton
        }
        .padding(.horizontal, 16)
        .padding(.top, 8)
        .padding(.bottom, 16)
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var backButton: some View {
        Button {
            dismiss()
        } label: {
            Image(systemName: "chevron.backward")
                .font(.body.weight(.semibold))
                .foregroundStyle(.white)
                .frame(minWidth: 44, minHeight: 44)
                .background(.black.opacity(0.45), in: Circle())
        }
        .buttonStyle(.plain)
        .accessibilityLabel("Back")
        .accessibilityIdentifier("voxelBackButton")
    }

    private var captureButton: some View {
        Button {
            session.saveCurrentFrame()
        } label: {
            Image(systemName: "camera.fill")
                .font(.title2)
                .frame(minWidth: 44, minHeight: 44)
        }
        .buttonStyle(.borderedProminent)
        .buttonBorderShape(.circle)
        .disabled(session.isSavingPhoto || session.runState != .running)
        .accessibilityLabel("Take picture")
        .accessibilityIdentifier("voxelCaptureButton")
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
            return "Voxel Eyes"
        }
    }
}

/// Hosts the session-owned `ARSCNView` in SwiftUI.
private struct VoxelARViewContainer: UIViewRepresentable {
    let view: ARSCNView

    func makeUIView(context: Context) -> ARSCNView { view }
    func updateUIView(_ uiView: ARSCNView, context: Context) {}
}

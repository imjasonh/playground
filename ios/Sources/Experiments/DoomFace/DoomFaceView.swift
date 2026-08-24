import SwiftUI
import UIKit

struct DoomFaceView: View {
    @StateObject private var session = DoomFaceSession()
    @State private var shareURL: ShareURL?
    @State private var exportError: String?

    var body: some View {
        VStack(spacing: 12) {
            camera
            sheet
            controls
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 8)
        .background(Color(red: 0.12, green: 0.02, blue: 0.02))
        .navigationTitle("Doom Face")
        .navigationBarTitleDisplayMode(.inline)
        .onAppear { session.start() }
        .onDisappear { session.stop() }
        .sheet(item: $shareURL) { item in
            ShareSheet(items: [item.url])
        }
        .alert("Export failed", isPresented: Binding(
            get: { exportError != nil },
            set: { if !$0 { exportError = nil } }
        )) {
            Button("OK", role: .cancel) { exportError = nil }
        } message: {
            Text(exportError ?? "")
        }
    }

    private var camera: some View {
        Color.black
            .aspectRatio(1, contentMode: .fit)
            .overlay {
                if let image = session.previewImage {
                    Image(uiImage: image)
                        .resizable()
                        .scaledToFill()
                        .accessibilityIdentifier("doomFacePreview")
                } else {
                    Text(placeholderText)
                        .font(.footnote)
                        .multilineTextAlignment(.center)
                        .foregroundStyle(.white.opacity(0.7))
                        .padding()
                        .accessibilityIdentifier("doomFacePlaceholder")
                }
            }
            .clipped()
            .overlay(alignment: .bottom) {
                VStack(spacing: 4) {
                    if let expression = session.liveExpression {
                        Text(expression.displayName)
                            .font(.caption.weight(.semibold))
                        ProgressView(value: session.holdProgress)
                            .tint(.orange)
                            .frame(width: 120)
                            .accessibilityIdentifier("doomFaceHoldProgress")
                    }
                    Text(session.statusMessage)
                        .font(.caption2)
                        .multilineTextAlignment(.center)
                        .accessibilityIdentifier("doomFaceStatusMessage")
                }
                .foregroundStyle(.white)
                .padding(8)
                .frame(maxWidth: .infinity)
                .background(.black.opacity(0.45))
            }
    }

    private var placeholderText: String {
        switch session.runState {
        case .unsupported, .failed:
            return session.statusMessage
        case .permissionDenied:
            return "Camera access is required. Enable it in Settings."
        case .requestingPermission:
            return "Requesting camera…"
        default:
            return "Starting front camera…"
        }
    }

    private var sheet: some View {
        VStack(alignment: .trailing, spacing: 4) {
            Text("\(session.filledCount)/\(session.totalSlots)")
                .font(.caption.monospacedDigit())
                .foregroundStyle(.white.opacity(0.65))
                .accessibilityIdentifier("doomFaceFillCount")

            Group {
                if let sheet = session.sheetImage {
                    Image(uiImage: sheet)
                        .resizable()
                        .interpolation(.none)
                        .scaledToFit()
                        .accessibilityIdentifier("doomFaceSheet")
                } else {
                    Color(white: 0.1)
                        .aspectRatio(640.0 / 396.0, contentMode: .fit)
                }
            }
        }
        .frame(maxHeight: .infinity)
    }

    private var controls: some View {
        HStack(spacing: 12) {
            Button {
                session.resetCaptures()
            } label: {
                Text("Reset")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.bordered)
            .tint(.white)
            .disabled(session.filledCount == 0)
            .accessibilityIdentifier("doomFaceReset")

            Button {
                do {
                    shareURL = ShareURL(url: try session.exportGIFURL())
                } catch {
                    exportError = error.localizedDescription
                }
            } label: {
                Text("Export GIF")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.borderedProminent)
            .tint(.orange)
            .disabled(!session.canExportGIF)
            .accessibilityIdentifier("doomFaceExport")
        }
    }
}

private struct ShareURL: Identifiable {
    let id = UUID()
    let url: URL
}

private struct ShareSheet: UIViewControllerRepresentable {
    let items: [Any]

    func makeUIViewController(context: Context) -> UIActivityViewController {
        UIActivityViewController(activityItems: items, applicationActivities: nil)
    }

    func updateUIViewController(_ controller: UIActivityViewController, context: Context) {}
}

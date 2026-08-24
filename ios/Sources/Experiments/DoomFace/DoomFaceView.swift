import SwiftUI
import UIKit

/// Square front-camera stage on top, doom face sheet below, export when ready.
struct DoomFaceView: View {
    @StateObject private var session = DoomFaceSession()
    @State private var sharePayload: SharePayload?
    @State private var exportError: String?

    var body: some View {
        VStack(spacing: 0) {
            cameraStage
            sheetStage
            controls
        }
        .background(Color(red: 0.12, green: 0.02, blue: 0.02))
        .navigationTitle("Doom Face")
        .navigationBarTitleDisplayMode(.inline)
        .onAppear { session.start() }
        .onDisappear { session.stop() }
        .sheet(item: $sharePayload) { payload in
            ShareSheet(items: [payload.url])
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

    // MARK: - Camera

    private var cameraStage: some View {
        GeometryReader { geo in
            let side = min(geo.size.width, geo.size.height)
            ZStack {
                Color.black
                Group {
                    if let image = session.previewImage {
                        Image(uiImage: image)
                            .resizable()
                            .scaledToFill()
                            .frame(width: side, height: side)
                            .clipped()
                            .accessibilityIdentifier("doomFacePreview")
                    } else {
                        placeholder
                            .frame(width: side, height: side)
                    }
                }
                .clipShape(Rectangle())
                .overlay {
                    Rectangle()
                        .strokeBorder(Color.white.opacity(0.35), lineWidth: 1)
                }
                .overlay(alignment: .bottom) {
                    expressionBanner
                }
                .overlay {
                    if session.captureFlash {
                        Color.white.opacity(0.35)
                            .allowsHitTesting(false)
                    }
                }
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
        .aspectRatio(1, contentMode: .fit)
        .padding(.horizontal, 16)
        .padding(.top, 8)
    }

    private var placeholder: some View {
        ZStack {
            Color(white: 0.08)
            VStack(spacing: 10) {
                Image(systemName: "face.dashed")
                    .font(.system(size: 36))
                    .foregroundStyle(.white.opacity(0.55))
                Text(placeholderText)
                    .font(.footnote)
                    .multilineTextAlignment(.center)
                    .foregroundStyle(.white.opacity(0.7))
                    .padding(.horizontal, 24)
            }
        }
        .accessibilityIdentifier("doomFacePlaceholder")
    }

    private var placeholderText: String {
        switch session.runState {
        case .unsupported:
            return session.statusMessage
        case .permissionDenied:
            return "Camera access is required. Enable it in Settings."
        case .requestingPermission:
            return "Requesting camera…"
        case .failed(let message):
            return message
        default:
            return "Starting front camera…"
        }
    }

    private var expressionBanner: some View {
        VStack(spacing: 6) {
            if let expression = session.liveExpression {
                Text(expression.displayName)
                    .font(.caption.weight(.semibold))
                    .foregroundStyle(.white)
                ProgressView(value: session.holdProgress)
                    .tint(.orange)
                    .frame(width: 120)
                    .opacity(session.holdProgress > 0 ? 1 : 0.35)
                    .accessibilityIdentifier("doomFaceHoldProgress")
            }
            Text(session.statusMessage)
                .font(.caption2)
                .foregroundStyle(.white.opacity(0.85))
                .multilineTextAlignment(.center)
                .padding(.horizontal, 10)
                .accessibilityIdentifier("doomFaceStatusMessage")
        }
        .padding(.vertical, 8)
        .padding(.horizontal, 12)
        .frame(maxWidth: .infinity)
        .background(Color.black.opacity(0.45))
    }

    // MARK: - Sheet

    private var sheetStage: some View {
        VStack(spacing: 6) {
            HStack {
                Text("Face sheet")
                    .font(.subheadline.weight(.semibold))
                    .foregroundStyle(.white.opacity(0.9))
                Spacer()
                Text("\(session.filledCount)/\(session.totalSlots)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.white.opacity(0.65))
                    .accessibilityIdentifier("doomFaceFillCount")
            }
            .padding(.horizontal, 16)

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
            .padding(.horizontal, 12)
            .overlay {
                if let slot = session.lastMatchedSlot, session.captureFlash {
                    GeometryReader { geo in
                        let rect = highlightedRect(for: slot, in: geo.size)
                        Rectangle()
                            .stroke(Color.orange, lineWidth: 2)
                            .frame(width: rect.width, height: rect.height)
                            .position(x: rect.midX, y: rect.midY)
                    }
                    .padding(.horizontal, 12)
                    .allowsHitTesting(false)
                }
            }
        }
        .padding(.top, 12)
        .frame(maxHeight: .infinity)
    }

    private func highlightedRect(for slot: DoomFaceSlot, in size: CGSize) -> CGRect {
        let sheet = DoomFaceSheetLayout.sheetSize
        let cell = DoomFaceSheetLayout.rect(for: slot)
        let scale = min(size.width / sheet.width, size.height / sheet.height)
        let drawSize = CGSize(width: sheet.width * scale, height: sheet.height * scale)
        let origin = CGPoint(
            x: (size.width - drawSize.width) / 2,
            y: (size.height - drawSize.height) / 2
        )
        return CGRect(
            x: origin.x + cell.minX * scale,
            y: origin.y + cell.minY * scale,
            width: cell.width * scale,
            height: cell.height * scale
        )
    }

    // MARK: - Controls

    private var controls: some View {
        HStack(spacing: 12) {
            Button {
                session.resetCaptures()
            } label: {
                Label("Reset", systemImage: "trash")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.bordered)
            .tint(.white)
            .disabled(session.filledCount == 0)
            .accessibilityIdentifier("doomFaceReset")

            Button {
                exportGIF()
            } label: {
                Label("Export GIF", systemImage: "square.and.arrow.up")
                    .frame(maxWidth: .infinity)
            }
            .buttonStyle(.borderedProminent)
            .tint(.orange)
            .disabled(!session.canExportGIF)
            .accessibilityIdentifier("doomFaceExport")
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 12)
    }

    private func exportGIF() {
        do {
            let url = try session.exportGIFURL()
            sharePayload = SharePayload(url: url)
        } catch {
            exportError = error.localizedDescription
        }
    }
}

// MARK: - Share helpers

private struct SharePayload: Identifiable {
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

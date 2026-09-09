import PhotosUI
import SwiftUI

/// Pick a photo, describe an edit, and compare the result with a pixel diff.
struct FaceSwapView: View {
    @StateObject private var session = FaceSwapSession()
    @State private var photoItem: PhotosPickerItem?

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 16) {
                modelBanner
                choosePhotoButton

                if session.resultImage == nil {
                    emptyState
                } else {
                    photoWell
                    if !session.outlines.isEmpty {
                        outlineList
                    }
                }

                promptField
                editButton

                Text(session.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .accessibilityIdentifier("faceSwapStatus")

                if session.hasEditResult {
                    resultControls
                }

                if !session.toolLog.isEmpty {
                    toolLog
                }
            }
            .padding()
        }
        .scrollDismissesKeyboard(.interactively)
        .onAppear {
            session.refreshModelStatus()
        }
        .onChange(of: photoItem) { item in
            guard let item else { return }
            Task {
                if let data = try? await item.loadTransferable(type: Data.self),
                   let image = UIImage(data: data)
                {
                    await session.load(image: image)
                } else {
                    session.statusMessage = "Could not read that photo."
                }
            }
        }
    }

    private var modelBanner: some View {
        VStack(alignment: .leading, spacing: 4) {
            Label(
                FaceSwapModelCopy.title(session.modelGate),
                systemImage: session.modelGate.isAvailable ? "checkmark.circle.fill" : "sparkles"
            )
            .font(.subheadline)
            .foregroundStyle(session.modelGate.isAvailable ? Color.green : Color.orange)
            if !session.modelGate.isAvailable {
                Text(FaceSwapModelCopy.detail(session.modelGate))
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .fixedSize(horizontal: false, vertical: true)
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityElement(children: .combine)
        .accessibilityIdentifier("faceSwapModelBanner")
    }

    private var choosePhotoButton: some View {
        PhotosPicker(selection: $photoItem, matching: .images) {
            Label("Choose Photo", systemImage: "photo")
                .frame(maxWidth: .infinity, minHeight: 44)
        }
        .buttonStyle(.bordered)
        .disabled(session.isRunning)
        .accessibilityIdentifier("faceSwapChoosePhoto")
    }

    private var emptyState: some View {
        VStack(spacing: 8) {
            Image(systemName: "person.crop.rectangle")
                .font(.largeTitle)
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            Text("No photo yet")
                .font(.headline)
        }
        .frame(maxWidth: .infinity)
        .padding(.vertical, 12)
        .accessibilityElement(children: .combine)
        .accessibilityIdentifier("faceSwapEmptyState")
    }

    private var photoWell: some View {
        Color.clear
            .aspectRatio(session.imageAspect, contentMode: .fit)
            .frame(maxWidth: .infinity, maxHeight: 420)
            .overlay {
                if let image = session.shownImage {
                    Image(uiImage: image)
                        .resizable()
                        .scaledToFill()
                }
            }
            .overlay {
                if session.viewMode != .diff {
                    outlineOverlay
                }
            }
            .clipShape(RoundedRectangle(cornerRadius: 8))
            .accessibilityElement(children: .ignore)
            .accessibilityLabel(session.imageAccessibilityLabel)
            .accessibilityIdentifier("faceSwapResultImage")
    }

    private var outlineOverlay: some View {
        GeometryReader { geo in
            ForEach(session.outlines) { outline in
                Path { path in
                    guard let first = outline.points.first else { return }
                    path.move(to: CGPoint(x: first.x * geo.size.width, y: first.y * geo.size.height))
                    for point in outline.points.dropFirst() {
                        path.addLine(to: CGPoint(x: point.x * geo.size.width, y: point.y * geo.size.height))
                    }
                    path.closeSubpath()
                }
                .stroke(outline.role == .destination ? Color.orange : Color.blue, lineWidth: outline.role == .destination ? 3 : 2)
                if let first = outline.points.first {
                    Text(outline.refersTo.isEmpty ? outline.role.rawValue : outline.refersTo)
                        .font(.caption2)
                        .padding(.horizontal, 6)
                        .padding(.vertical, 2)
                        .background(.thinMaterial, in: Capsule())
                        .position(
                            x: min(geo.size.width - 24, max(24, first.x * geo.size.width)),
                            y: min(geo.size.height - 12, max(12, first.y * geo.size.height))
                        )
                }
            }
        }
        .allowsHitTesting(false)
        .accessibilityHidden(true)
    }

    private var outlineList: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text("Chosen regions")
                .font(.subheadline)
            ForEach(session.outlines) { outline in
                Text(outline.displayLine)
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("faceSwapOutlineList")
    }

    private var promptField: some View {
        TextField("Describe the edit", text: $session.prompt, axis: .vertical)
            .lineLimit(2...4)
            .textFieldStyle(.roundedBorder)
            .disabled(session.isRunning)
            .accessibilityIdentifier("faceSwapPrompt")
    }

    private var editButton: some View {
        Button {
            Task { await session.edit() }
        } label: {
            if session.isRunning {
                ProgressView()
                    .frame(maxWidth: .infinity, minHeight: 44)
            } else {
                Text("Edit")
                    .frame(maxWidth: .infinity, minHeight: 44)
            }
        }
        .buttonStyle(.borderedProminent)
        .disabled(!session.canEdit)
        .accessibilityLabel("Edit")
        .accessibilityIdentifier("faceSwapEditButton")
    }

    private var resultControls: some View {
        VStack(alignment: .leading, spacing: 12) {
            Picker("View", selection: $session.viewMode) {
                ForEach(FaceSwapViewMode.allCases) { mode in
                    Text(mode.title).tag(mode)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("faceSwapViewMode")

            HStack(spacing: 12) {
                Button("Revert") {
                    session.revert()
                }
                .buttonStyle(.bordered)
                .frame(minHeight: 44)
                .accessibilityIdentifier("faceSwapRevertButton")

                if let shareURL = session.shareURL {
                    ShareLink(item: shareURL) {
                        Label("Share", systemImage: "square.and.arrow.up")
                            .frame(minHeight: 44)
                    }
                    .buttonStyle(.bordered)
                    .accessibilityLabel("Share")
                    .accessibilityIdentifier("faceSwapShareButton")
                }
            }
        }
    }

    private var toolLog: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text("Tools")
                .font(.subheadline)
            ForEach(Array(session.toolLog.suffix(8).enumerated()), id: \.offset) { _, line in
                Text(line)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("faceSwapToolLog")
    }
}

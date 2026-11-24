import CoreGraphics
import PhotosUI
import SwiftUI
#if canImport(UIKit)
import UIKit
#endif

/// Photo picker, live 800×480 e-paper quantization/dithering preview, and BLE upload
/// controls for the Waveshare 7.5″ V2 (`waveshare-epd75-photo`) firmware app.
struct MCULabPhotoFramePanel: View {
    @ObservedObject var controller: MCULabController

    private struct LoadedPhoto: Identifiable, Sendable {
        let id = UUID()
        let source: CGImage
        var processed: MCULabProcessedPhoto?
        var preview: CGImage?
    }

    private enum RotationInterval: UInt32, CaseIterable, Identifiable {
        case oneMinute = 60
        case fiveMinutes = 300
        case tenMinutes = 600
        case thirtyMinutes = 1_800
        case oneHour = 3_600
        case manual = 0

        var id: UInt32 { rawValue }

        var label: String {
            switch self {
            case .oneMinute: return "1 min"
            case .fiveMinutes: return "5 min"
            case .tenMinutes: return "10 min"
            case .thirtyMinutes: return "30 min"
            case .oneHour: return "1 hour"
            case .manual: return "Manual only"
            }
        }
    }

    @State private var pickerItems: [PhotosPickerItem] = []
    @State private var photos: [LoadedPhoto] = []
    @State private var selectedIndex: Int = 0
    @State private var options = MCULabPhotoOptions()
    @State private var rotationInterval: RotationInterval = .tenMinutes
    @State private var isProcessing = false
    @State private var showFineTune = false
    @State private var compressedEstimateBytes: Int?
    @State private var processingTask: Task<Void, Never>?

    private var isUploadingPhotos: Bool {
        controller.otaTransferKind == .dataBlob && controller.otaPhase.isActive
    }

    private var readyFrames: [Data] {
        photos.compactMap { $0.processed?.frameData }
    }

    private var rawAlbumBytes: Int {
        guard !readyFrames.isEmpty else { return 0 }
        return MCULabPhotoProcessor.headerLength + readyFrames.count * options.mode.frameBytes
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Text("Waveshare Photo Frame")
                    .font(.subheadline.bold())
                Spacer()
                if !photos.isEmpty {
                    Text("\(photos.count)/\(options.mode.maxPhotos)")
                        .font(.caption.monospacedDigit())
                        .foregroundStyle(.secondary)
                }
            }

            HStack(spacing: 8) {
                PhotosPicker(
                    selection: $pickerItems,
                    maxSelectionCount: options.mode.maxPhotos,
                    matching: .images,
                    photoLibrary: .shared()
                ) {
                    Label(
                        photos.isEmpty ? "Choose Photos" : "Choose Photos (\(photos.count))",
                        systemImage: "photo.on.rectangle.angled"
                    )
                    .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("mcuLabPhotoPickButton")

                if !photos.isEmpty {
                    Button(role: .destructive) {
                        clearPhotos()
                    } label: {
                        Image(systemName: "trash")
                            .frame(minWidth: 44, minHeight: 44)
                    }
                    .buttonStyle(.bordered)
                    .accessibilityLabel("Clear selected photos")
                    .accessibilityIdentifier("mcuLabPhotoClearButton")
                }
            }

            if !photos.isEmpty {
                previewSection
                controlsSection
                uploadSection
            } else {
                Text("Pick 1 or more photos to quantize and dither at 800×480 for the Waveshare 7.5″ display. Multiple photos automatically rotate every 10 minutes.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabPhotoEmptyHint")
            }

            if controller.otaTransferKind == .dataBlob, !controller.otaStatusText.isEmpty {
                Text(controller.otaStatusText)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabPhotoStatusText")
            }
        }
        .padding(12)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 12))
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("mcuLabPhotoFramePanel")
        .onChange(of: pickerItems) { _, newItems in
            loadSelectedPhotos(newItems)
        }
        .onChange(of: options) { _, _ in
            if photos.count > options.mode.maxPhotos {
                photos = Array(photos.prefix(options.mode.maxPhotos))
                selectedIndex = min(selectedIndex, max(0, photos.count - 1))
            }
            reprocessAllPhotos()
        }
        .onDisappear {
            processingTask?.cancel()
        }
    }

    @ViewBuilder
    private var previewSection: some View {
        let clampedIndex = min(selectedIndex, max(0, photos.count - 1))
        VStack(alignment: .leading, spacing: 8) {
            ZStack {
                RoundedRectangle(cornerRadius: 8)
                    .fill(Color(white: 0.94))
                if let preview = photos[clampedIndex].preview {
                    Image(decorative: preview, scale: 1.0)
                        .interpolation(.none)
                        .resizable()
                        .aspectRatio(
                            CGFloat(MCULabPhotoProcessor.panelWidth) / CGFloat(MCULabPhotoProcessor.panelHeight),
                            contentMode: .fit
                        )
                        .clipShape(RoundedRectangle(cornerRadius: 6))
                        .padding(4)
                } else {
                    ProgressView("Dithering 800×480…")
                        .font(.caption)
                }
            }
            .aspectRatio(800.0 / 480.0, contentMode: .fit)
            .overlay(
                RoundedRectangle(cornerRadius: 8)
                    .stroke(Color.primary.opacity(0.2), lineWidth: 1)
            )
            .accessibilityIdentifier("mcuLabPhotoPreview")

            if photos.count > 1 {
                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 8) {
                        ForEach(Array(photos.enumerated()), id: \.element.id) { idx, item in
                            Button {
                                selectedIndex = idx
                            } label: {
                                ZStack(alignment: .topLeading) {
                                    if let thumb = item.preview {
                                        Image(decorative: thumb, scale: 1.0)
                                            .interpolation(.none)
                                            .resizable()
                                            .aspectRatio(800.0 / 480.0, contentMode: .fill)
                                            .frame(width: 72, height: 44)
                                            .clipped()
                                            .clipShape(RoundedRectangle(cornerRadius: 6))
                                    } else {
                                        RoundedRectangle(cornerRadius: 6)
                                            .fill(Color.secondary.opacity(0.2))
                                            .frame(width: 72, height: 44)
                                    }
                                    Text("\(idx + 1)")
                                        .font(.caption2.bold().monospacedDigit())
                                        .padding(.horizontal, 4)
                                        .padding(.vertical, 1)
                                        .background(.ultraThinMaterial, in: Capsule())
                                        .padding(3)
                                }
                                .overlay(
                                    RoundedRectangle(cornerRadius: 6)
                                        .stroke(
                                            idx == clampedIndex ? Color.accentColor : Color.clear,
                                            lineWidth: 2
                                        )
                                )
                            }
                            .buttonStyle(.plain)
                        }
                    }
                }
            }
        }
    }

    private var controlsSection: some View {
        VStack(alignment: .leading, spacing: 8) {
            Picker("Display Mode", selection: $options.mode) {
                ForEach(MCULabPhotoMode.allCases) { mode in
                    Text(mode.displayName).tag(mode)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("mcuLabPhotoModePicker")

            Picker("Dithering", selection: $options.dither) {
                ForEach(MCULabPhotoDitherAlgorithm.allCases) { algo in
                    Text(algo.displayName).tag(algo)
                }
            }
            .pickerStyle(.menu)
            .accessibilityIdentifier("mcuLabPhotoDitherPicker")

            Picker("Framing", selection: $options.fit) {
                ForEach(MCULabPhotoFitMode.allCases) { fit in
                    Text(fit.displayName).tag(fit)
                }
            }
            .pickerStyle(.menu)
            .accessibilityIdentifier("mcuLabPhotoFitPicker")

            if photos.count > 1 {
                Picker("Rotate every", selection: $rotationInterval) {
                    ForEach(RotationInterval.allCases) { interval in
                        Text(interval.label).tag(interval)
                    }
                }
                .pickerStyle(.menu)
                .accessibilityIdentifier("mcuLabPhotoIntervalPicker")
            }

            DisclosureGroup("Fine-tune tone & sharpening", isExpanded: $showFineTune) {
                VStack(alignment: .leading, spacing: 8) {
                    Toggle("Auto-contrast (1%–99% stretch)", isOn: $options.autoContrast)
                    Toggle("Rotate portrait photos 90°", isOn: $options.rotatePortrait)

                    VStack(alignment: .leading, spacing: 2) {
                        HStack {
                            Text("Sharpening")
                                .font(.caption)
                            Spacer()
                            Text("\(Int((options.sharpenAmount * 100).rounded()))%")
                                .font(.caption.monospacedDigit())
                                .foregroundStyle(.secondary)
                        }
                        Slider(value: $options.sharpenAmount, in: 0...1, step: 0.05)
                    }

                    VStack(alignment: .leading, spacing: 2) {
                        HStack {
                            Text("Midtone gamma")
                                .font(.caption)
                            Spacer()
                            Text(String(format: "%.2f", options.gamma))
                                .font(.caption.monospacedDigit())
                                .foregroundStyle(.secondary)
                        }
                        Slider(value: $options.gamma, in: 0.6...1.6, step: 0.05)
                    }
                }
                .padding(.top, 4)
            }
            .font(.caption)
        }
    }

    private var uploadSection: some View {
        VStack(alignment: .leading, spacing: 8) {
            if rawAlbumBytes > 0 {
                let rawKB = rawAlbumBytes / 1024
                let wireText: String = if let est = compressedEstimateBytes {
                    " (~\(max(1, est / 1024)) KB over BLE)"
                } else {
                    ""
                }
                let rotateText: String = if photos.count > 1, rotationInterval != .manual {
                    " · rotates every \(rotationInterval.label)"
                } else {
                    ""
                }
                Text("\(readyFrames.count) \(readyFrames.count == 1 ? "photo" : "photos") · \(rawKB) KB\(wireText)\(rotateText)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabPhotoSizeSummary")
            }

            if isUploadingPhotos, case .streaming(let written, let total) = controller.otaPhase, total > 0 {
                let fraction = Double(written) / Double(total)
                ProgressView(value: min(max(fraction, 0), 1))
                    .accessibilityLabel("Photo transfer progress")
                    .accessibilityValue("\(Int((fraction * 100).rounded())) percent")
                    .accessibilityIdentifier("mcuLabPhotoProgressView")
            }

            if isUploadingPhotos {
                Button(role: .destructive) {
                    controller.cancelOTAUpdate()
                } label: {
                    Label("Cancel Photo Transfer", systemImage: "xmark.circle.fill")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("mcuLabPhotoCancelButton")
            } else {
                Button {
                    sendPhotosToDisplay()
                } label: {
                    Label(
                        photos.count == 1
                            ? "Send Photo to Display"
                            : "Send \(photos.count) Photos to Display",
                        systemImage: "photo.badge.arrow.down.fill"
                    )
                    .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .disabled(isProcessing || readyFrames.count != photos.count || controller.otaPhase.isActive)
                .accessibilityIdentifier("mcuLabPhotoSendButton")
            }
        }
    }

    private func clearPhotos() {
        processingTask?.cancel()
        pickerItems = []
        photos = []
        selectedIndex = 0
        compressedEstimateBytes = nil
        isProcessing = false
    }

    private func loadSelectedPhotos(_ items: [PhotosPickerItem]) {
        processingTask?.cancel()
        guard !items.isEmpty else {
            photos = []
            selectedIndex = 0
            compressedEstimateBytes = nil
            isProcessing = false
            return
        }
        isProcessing = true
        let currentOptions = options
        processingTask = Task {
            var loaded: [LoadedPhoto] = []
            for item in items {
                if Task.isCancelled { return }
                guard let data = try? await item.loadTransferable(type: Data.self) else {
                    continue
                }
                #if canImport(UIKit)
                guard let uiImage = UIImage(data: data),
                      let cg = MCULabPhotoProcessor.uprightCGImage(from: uiImage)
                else {
                    continue
                }
                loaded.append(LoadedPhoto(source: cg, processed: nil, preview: nil))
                #endif
            }
            if Task.isCancelled { return }
            await MainActor.run {
                self.photos = loaded
                self.selectedIndex = 0
            }
            await processLoadedPhotos(loaded, options: currentOptions)
        }
    }

    private func reprocessAllPhotos() {
        processingTask?.cancel()
        let currentPhotos = photos
        guard !currentPhotos.isEmpty else {
            compressedEstimateBytes = nil
            isProcessing = false
            return
        }
        isProcessing = true
        let currentOptions = options
        processingTask = Task {
            await processLoadedPhotos(currentPhotos, options: currentOptions)
        }
    }

    private func processLoadedPhotos(_ sourcePhotos: [LoadedPhoto], options: MCULabPhotoOptions) async {
        let intervalSecs = rotationInterval.rawValue
        let processedResult = await Task.detached(priority: .userInitiated) {
            () -> ([LoadedPhoto], Int?) in
            var updated = sourcePhotos
            var frames: [Data] = []
            for i in 0..<updated.count {
                if Task.isCancelled { return (updated, nil) }
                if let result = MCULabPhotoProcessor.process(cgImage: updated[i].source, options: options) {
                    let preview = MCULabPhotoProcessor.makePreviewCGImage(levels: result.levels)
                    updated[i].processed = result
                    updated[i].preview = preview
                    frames.append(result.frameData)
                }
            }
            var compressedSize: Int? = nil
            if let album = MCULabPhotoProcessor.encodeAlbum(
                mode: options.mode,
                intervalSecs: intervalSecs,
                frames: frames
            ) {
                compressedSize = MCULabProtocol.deflateCompress(album)?.count ?? album.count
            }
            return (updated, compressedSize)
        }.value

        if Task.isCancelled { return }
        await MainActor.run {
            self.photos = processedResult.0
            self.compressedEstimateBytes = processedResult.1
            self.isProcessing = false
        }
    }

    private func sendPhotosToDisplay() {
        let frames = readyFrames
        guard !frames.isEmpty else { return }
        let interval = frames.count > 1 ? rotationInterval.rawValue : 0
        guard let albumData = MCULabPhotoProcessor.encodeAlbum(
            mode: options.mode,
            intervalSecs: interval,
            frames: frames
        ) else {
            return
        }
        let label = frames.count == 1
            ? "1 photo (\(options.mode.displayName))"
            : "\(frames.count) photos (\(options.mode.displayName))"
        controller.armDataBlobUpload(
            data: albumData,
            name: label,
            targetBoard: .waveshareEPD75
        )
    }
}

import Foundation
import UIKit
import FoundationModels

/// The on-device model chooses which edit tools to call. Each tool writes
/// only inside the regions it names.
@MainActor
final class FaceSwapSession: ObservableObject {
    @Published var prompt = "Swap the man's face onto the woman's body"
    @Published var statusMessage = "Choose a photo."
    @Published var modelGate: AgentModelGate
    @Published var outlines: [FaceSwapOutline] = []
    @Published var toolLog: [String] = []
    @Published var isRunning = false
    @Published var viewMode: FaceSwapViewMode = .result
    @Published var resultImage: UIImage?
    @Published var diffImage: UIImage?
    @Published var imageAspect: CGFloat = 1
    @Published var hasEditResult = false
    @Published var lastStats: FaceSwapEditStats?
    @Published var shareURL: URL?

    private var originalRaster: FaceSwapRaster?
    private var workingRaster: FaceSwapRaster?

    var shownImage: UIImage? {
        if viewMode == .diff, let diffImage {
            return diffImage
        }
        return resultImage
    }

    var canEdit: Bool {
        guard !isRunning, originalRaster != nil, modelGate.isAvailable else { return false }
        return !prompt.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
    }

    var imageAccessibilityLabel: String {
        if viewMode == .diff, hasEditResult {
            return "Pixel diff. Changed pixels are red. Unchanged pixels are gray. \(statusMessage)"
        }
        if hasEditResult {
            return "Edited photo. \(statusMessage)"
        }
        return "Chosen photo"
    }

    init() {
        modelGate = Self.readGate()
    }

    func refreshModelStatus() {
        modelGate = Self.readGate()
    }

    func load(image: UIImage) async {
        refreshModelStatus()
        guard let decoded = FaceSwapRaster.decode(image, maxEdge: 1_024) else {
            statusMessage = "Could not read that photo."
            return
        }
        originalRaster = decoded.raster
        workingRaster = decoded.raster
        outlines = []
        lastStats = nil
        toolLog = []
        hasEditResult = false
        viewMode = .result
        shareURL = nil
        imageAspect = CGFloat(decoded.raster.width) / CGFloat(max(decoded.raster.height, 1))
        resultImage = decoded.raster.uiImage()
        diffImage = nil
        writeShareFile()
        var note = "Photo ready."
        if decoded.wasScaled {
            note += " Working copy long edge is \(max(decoded.raster.width, decoded.raster.height)) px."
        }
        statusMessage = note
    }

    func edit() async {
        guard canEdit, let original = originalRaster else { return }
        isRunning = true
        defer { isRunning = false }
        workingRaster = original
        outlines = []
        lastStats = nil
        toolLog = []
        hasEditResult = false
        viewMode = .result
        shareURL = nil
        publishDisplay()

        do {
            statusMessage = "Choosing targeted edits…"
            let result = try await FaceSwapToolSession.run(request: prompt, raster: original)
            outlines = result.outlines
            toolLog.append(contentsOf: result.log)
            workingRaster = result.image
            lastStats = result.stats
            toolLog.append(FaceSwapDiff.summary(original: original, edited: result.image))
            toolLog.append("0 pixels outside the chosen regions changed.")
            statusMessage = FaceSwapDiff.summary(original: original, edited: result.image)
            hasEditResult = true
        } catch FaceSwapModelError.missingEditPlan {
            statusMessage = "The model did not choose an edit. No pixels changed."
        } catch {
            statusMessage = FaceSwapModelLimits.failure(error).localizedDescription
        }
        publishDisplay()
        writeShareFile()
    }

    func revert() {
        workingRaster = originalRaster
        outlines = []
        lastStats = nil
        toolLog = []
        hasEditResult = false
        viewMode = .result
        shareURL = nil
        statusMessage = "Reverted to the original photo."
        publishDisplay()
        writeShareFile()
    }

    func saveToPhotos() async {
        guard let image = workingRaster?.uiImage() else {
            statusMessage = "Choose a photo first."
            return
        }
        do {
            try await FaceSwapPhotoSaver.saveJPEG(image)
            statusMessage = "Saved to Photos."
        } catch {
            statusMessage = error.localizedDescription
        }
    }

    private func publishDisplay() {
        resultImage = (workingRaster ?? originalRaster)?.uiImage()
        if let original = originalRaster, let working = workingRaster, lastStats != nil {
            diffImage = FaceSwapDiff.highlight(original: original, edited: working).uiImage()
        } else {
            diffImage = nil
        }
    }

    private func writeShareFile() {
        guard let working = workingRaster,
              let data = working.uiImage()?.jpegData(compressionQuality: 0.92)
        else {
            shareURL = nil
            return
        }
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("face-swap-\(UUID().uuidString)")
            .appendingPathExtension("jpg")
        do {
            try data.write(to: url, options: .atomic)
            shareURL = url
        } catch {
            shareURL = nil
        }
    }

    private static func readGate() -> AgentModelGate {
        switch SystemLanguageModel.default.availability {
        case .available:
            return .available
        case .unavailable(.deviceNotEligible):
            return .deviceNotEligible
        case .unavailable(.appleIntelligenceNotEnabled):
            return .needsAppleIntelligence
        case .unavailable(.modelNotReady):
            return .modelNotReady
        case .unavailable(let reason):
            return .other("Apple Intelligence isn't available (\(String(describing: reason))).")
        @unknown default:
            return .other("Apple Intelligence isn't available on this device.")
        }
    }
}

struct FaceSwapOutlineFailure: LocalizedError {
    var message: String
    var errorDescription: String? { message }
}

enum FaceSwapModelCopy {
    static func title(_ gate: AgentModelGate) -> String {
        switch gate {
        case .available:
            return "On-device model ready"
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence"
        case .modelNotReady:
            return "Model still downloading"
        case .deviceNotEligible:
            return "Device not eligible"
        case .other:
            return "Apple Intelligence unavailable"
        }
    }

    static func detail(_ gate: AgentModelGate) -> String {
        switch gate {
        case .available:
            return "The session calls tools that write only inside named regions."
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence, then come back."
        case .modelNotReady:
            return "Apple Intelligence is on, but the on-device model is still downloading."
        case .deviceNotEligible:
            return "This iPhone doesn't support Apple Intelligence."
        case .other(let reason):
            return reason
        }
    }
}

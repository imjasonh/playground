import Foundation
import UIKit

#if canImport(FoundationModels)
import FoundationModels
#endif

/// The on-device model chooses which edit tools to call. Each tool writes
/// only inside the regions it names.
@MainActor
final class FaceSwapSession: ObservableObject {
    @Published var prompt = "Swap the man's face onto the woman's body"
    @Published var statusMessage = "Choose a photo."
    @Published var modelGate: AgentModelGate
    @Published var outlines: [FaceSwapOutline] = []
    @Published var toolLog: [String] = []
    @Published var modelReply = ""
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
        if #available(iOS 26.0, *) {
            modelGate = Self.readGate()
        } else {
            modelGate = .unsupportedPlatform
        }
    }

    func refreshModelStatus() {
        if #available(iOS 26.0, *) {
            modelGate = Self.readGate()
        } else {
            modelGate = .unsupportedPlatform
        }
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
        modelReply = ""
        hasEditResult = false
        viewMode = .result
        shareURL = nil
        imageAspect = CGFloat(decoded.raster.width) / CGFloat(max(decoded.raster.height, 1))
        resultImage = decoded.raster.uiImage()
        diffImage = nil
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
        modelReply = ""
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
            statusMessage = result.log.joined(separator: ". ") + ". "
                + FaceSwapDiff.summary(original: original, edited: result.image)
                + " 0 pixels outside the chosen regions changed."
            modelReply = result.outlines.map(\.refersTo).filter { !$0.isEmpty }.joined(separator: ", ")
            hasEditResult = true
        } catch FaceSwapImageError.missingEditPlan {
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
        modelReply = ""
        hasEditResult = false
        viewMode = .result
        shareURL = nil
        statusMessage = "Reverted to the original photo."
        publishDisplay()
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
        guard let working = workingRaster, lastStats != nil,
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
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
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
                return .other("Apple Intelligence isn’t available (\(String(describing: reason))).")
            @unknown default:
                return .other("Apple Intelligence isn’t available on this device.")
            }
        }
        #endif
        return .unsupportedPlatform
    }
}

struct FaceSwapOutlineFailure: LocalizedError {
    var message: String
    var errorDescription: String? { message }
}

enum FaceSwapModelCopy {
    static func title(_ gate: AgentModelGate, canAttachImages _: Bool) -> String {
        switch gate {
        case .available:
            return "On-device model ready"
        case .needsAppleIntelligence:
            return "Turn on Apple Intelligence"
        case .modelNotReady:
            return "Model still downloading"
        case .deviceNotEligible:
            return "Device not eligible"
        case .unsupportedPlatform:
            return "Needs iOS 26+"
        case .other:
            return "Apple Intelligence unavailable"
        }
    }

    static func detail(_ gate: AgentModelGate, canAttachImages: Bool) -> String {
        switch gate {
        case .available:
            if canAttachImages {
                return "The model sees a small preview, then calls tools that write only inside named regions."
            }
            return "The model chooses tools from the regions in the photo. Each tool writes only inside those regions."
        case .needsAppleIntelligence:
            return "Face Swap uses the on-device model to choose the faces. Turn on Apple Intelligence, then come back."
        case .modelNotReady:
            return "Apple Intelligence is on, but the on-device model is still downloading."
        case .deviceNotEligible:
            return "This hardware doesn’t support Apple Intelligence, so Face Swap can’t choose faces here."
        case .unsupportedPlatform:
            return "The model needs iOS 26 or later."
        case .other(let reason):
            return reason
        }
    }
}

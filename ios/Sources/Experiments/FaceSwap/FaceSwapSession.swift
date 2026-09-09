import Foundation
import UIKit

#if canImport(FoundationModels)
import FoundationModels
#endif

/// The on-device model traces face outlines, then chooses a reconstruction
/// that is applied only inside the destination outline.
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
    private var didRetryOutline = false

    var shownImage: UIImage? {
        if viewMode == .diff, let diffImage {
            return diffImage
        }
        return resultImage
    }

    var canUseImageModel: Bool {
        modelGate.isAvailable && FaceSwapImagePromptSupport.canAttachImages
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
        didRetryOutline = false
        shareURL = nil
        publishDisplay()

        do {
            if FaceSwapImagePromptSupport.canAttachImages {
                try await editFromImage(request: prompt, raster: original)
            } else {
                try await editFromContours(request: prompt, raster: original)
            }
        } catch FaceSwapImageError.imageInputUnavailable where FaceSwapImagePromptSupport.canAttachImages {
            do {
                try await editFromContours(request: prompt, raster: original)
            } catch {
                statusMessage = error.localizedDescription
            }
        } catch FaceSwapImageError.emptyOutlines {
            statusMessage = "The model did not return face outlines."
        } catch FaceSwapImageError.missingEditPlan {
            statusMessage = "The model did not choose an edit. No pixels changed."
        } catch {
            if isContextOverflow(error), !didRetryOutline {
                didRetryOutline = true
                toolLog.append("Context was full. Started a new session and retrying.")
                workingRaster = original
                do {
                    if FaceSwapImagePromptSupport.canAttachImages {
                        try await editFromImage(request: prompt, raster: original)
                    } else {
                        try await editFromContours(request: prompt, raster: original)
                    }
                } catch {
                    statusMessage = error.localizedDescription
                }
            } else {
                statusMessage = error.localizedDescription
            }
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

    private func editFromImage(request: String, raster: FaceSwapRaster) async throws {
        statusMessage = "Tracing face outlines…"
        let traced = try await traceOutlines(request: request, raster: raster)
        outlines = traced
        toolLog.append(contentsOf: traced.map { "outline \($0.displayLine)" })
        statusMessage = "Choosing the edit inside those outlines…"
        let plan = try await choosePlan(request: request, outlines: traced, raster: raster)
        try apply(plan: plan, outlines: traced, original: raster)
    }

    private func editFromContours(request: String, raster: FaceSwapRaster) async throws {
        statusMessage = "Reading face contours…"
        let decision = try await FaceSwapTextPrompt.decide(request: request, raster: raster)
        outlines = decision.outlines
        toolLog.append("iOS 26 contours. The model chose among traced faces. It did not see the photo.")
        toolLog.append(contentsOf: decision.outlines.map { "outline \($0.displayLine)" })
        let recipe = decision.plan.clamped()
        var line = String(
            format: "assignFaces fit=%.2f light=%.2f color=%.2f detail=%.2f edge=%.2f inset=%.2f",
            recipe.fitPose,
            recipe.lightingMatch,
            recipe.colorMatch,
            recipe.detailTransfer,
            recipe.edgeBand,
            recipe.inset
        )
        if !recipe.motive.isEmpty {
            line += " — \(recipe.motive)"
        }
        toolLog.append(line)
        statusMessage = "Reconstructing inside the chosen contour…"
        try apply(plan: decision.plan, outlines: decision.outlines, original: raster)
    }

    private func traceOutlines(request: String, raster: FaceSwapRaster) async throws -> [FaceSwapOutline] {
        guard let preview = FaceSwapImagePrompt.previewImage(from: raster) else {
            throw FaceSwapImageError.imageInputUnavailable
        }
        let traced = try await FaceSwapImagePrompt.findOutlines(preview: preview, request: request)
        switch FaceSwapOutlineValidation.prepare(traced) {
        case .success(let pair):
            return [pair.source, pair.destination]
        case .failure(let message):
            if didRetryOutline {
                throw FaceSwapOutlineFailure(message: message)
            }
            didRetryOutline = true
            toolLog.append(message)
            let tightened = try await FaceSwapImagePrompt.findOutlines(
                preview: preview,
                request: "\(request)\n\(message) Trace only the face skin."
            )
            switch FaceSwapOutlineValidation.prepare(tightened) {
            case .success(let pair):
                return [pair.source, pair.destination]
            case .failure(let retryMessage):
                throw FaceSwapOutlineFailure(message: retryMessage)
            }
        }
    }

    private func choosePlan(
        request: String,
        outlines: [FaceSwapOutline],
        raster: FaceSwapRaster
    ) async throws -> FaceSwapEditPlan {
        guard let source = outlines.first(where: { $0.role == .source }),
              let destination = outlines.first(where: { $0.role == .destination }),
              let sourceCrop = FaceSwapImagePrompt.crop(raster, outline: source, padding: 0.12),
              let destinationCrop = FaceSwapImagePrompt.crop(raster, outline: destination, padding: 0.12)
        else {
            throw FaceSwapOutlineFailure(message: "Could not crop the outlined faces.")
        }
        let plan = try await FaceSwapImagePrompt.editPlan(
            request: request,
            outlines: outlines,
            sourceCrop: sourceCrop,
            destinationCrop: destinationCrop
        )
        let recipe = plan.clamped()
        var line = String(
            format: "applyRegionEdit fit=%.2f light=%.2f color=%.2f detail=%.2f edge=%.2f inset=%.2f",
            recipe.fitPose,
            recipe.lightingMatch,
            recipe.colorMatch,
            recipe.detailTransfer,
            recipe.edgeBand,
            recipe.inset
        )
        if !recipe.motive.isEmpty {
            line += " — \(recipe.motive)"
        }
        toolLog.append(line)
        return plan
    }

    private func apply(plan: FaceSwapEditPlan, outlines: [FaceSwapOutline], original: FaceSwapRaster) throws {
        guard let source = outlines.first(where: { $0.role == .source }),
              let destination = outlines.first(where: { $0.role == .destination }),
              let working = workingRaster
        else {
            throw FaceSwapOutlineFailure(message: "Missing source or destination outline.")
        }
        let landmarks = FaceSwapLandmarks.locate(raster: original)
        let output = FaceSwapEditor.apply(
            plan: plan,
            source: source,
            destination: destination,
            original: original,
            working: working,
            sourceLandmarks: FaceSwapLandmarks.trio(inside: source, candidates: landmarks, width: original.width, height: original.height),
            destinationLandmarks: FaceSwapLandmarks.trio(inside: destination, candidates: landmarks, width: original.width, height: original.height)
        )
        switch output {
        case .success(let paste):
            guard paste.stats.outsideMaskChanged == 0 else {
                throw FaceSwapOutlineFailure(message: "The edit changed pixels outside the destination outline. Nothing was kept.")
            }
            let fraction = Double(paste.stats.changedFromOriginal) / Double(max(paste.stats.totalPixels, 1))
            guard fraction <= 0.22 else {
                throw FaceSwapOutlineFailure(message: "The edit changed too much of the photo. Nothing was kept.")
            }
            workingRaster = paste.image
            lastStats = paste.stats
            toolLog.append(FaceSwapEditor.resultMessage(paste.stats, plan: plan))
            let named = outlines.map(\.refersTo).filter { !$0.isEmpty }.joined(separator: " and ")
            let who = named.isEmpty ? "the outlined faces" : named
            statusMessage = "Outlined \(who). " + FaceSwapDiff.summary(original: original, edited: paste.image)
                + " 0 pixels outside the destination outline changed."
            modelReply = plan.clamped().motive
            hasEditResult = true
        case .failure(let message):
            throw FaceSwapOutlineFailure(message: message)
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

    private func isContextOverflow(_ error: Error) -> Bool {
        OnDeviceContextManager.isExceededContextWindow(error)
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
                return "The model traces face outlines, then reconstructs only inside the destination outline."
            }
            return "The model chooses among face contours, then reconstructs only inside the destination contour."
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

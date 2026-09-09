import Foundation
import UIKit

#if canImport(FoundationModels)
import FoundationModels
#endif

enum FaceSwapImageError: Error, Equatable {
    case imageInputUnavailable
    case emptyOutlines
    case missingEditPlan
}

/// Image attachments exist on the iOS 27 on-device model. Older SDKs compile
/// without that type, and the experiment refuses to invent outlines instead.
enum FaceSwapImagePromptSupport {
    static var canAttachImages: Bool {
        #if compiler(>=6.3) && canImport(FoundationModels)
        if #available(iOS 27.0, *) {
            return true
        }
        #endif
        return false
    }
}

enum FaceSwapImagePrompt {
    static let previewLongEdge = 512
    static let cropLongEdge = 256

    static func findOutlines(preview: UIImage, request: String) async throws -> [FaceSwapOutline] {
        #if compiler(>=6.3) && canImport(FoundationModels)
        if #available(iOS 27.0, *) {
            return try await FaceSwapImageSession.findOutlines(preview: preview, request: request)
        }
        #endif
        throw FaceSwapImageError.imageInputUnavailable
    }

    static func editPlan(
        request: String,
        outlines: [FaceSwapOutline],
        sourceCrop: UIImage,
        destinationCrop: UIImage
    ) async throws -> FaceSwapEditPlan {
        #if compiler(>=6.3) && canImport(FoundationModels)
        if #available(iOS 27.0, *) {
            return try await FaceSwapImageSession.editPlan(
                request: request,
                outlines: outlines,
                sourceCrop: sourceCrop,
                destinationCrop: destinationCrop
            )
        }
        #endif
        throw FaceSwapImageError.imageInputUnavailable
    }

    static func previewImage(from raster: FaceSwapRaster) -> UIImage? {
        guard let decoded = FaceSwapRaster.decode(raster.uiImage() ?? UIImage(), maxEdge: previewLongEdge) else {
            return raster.uiImage()
        }
        return decoded.raster.uiImage()
    }

    static func crop(_ raster: FaceSwapRaster, outline: FaceSwapOutline, padding: CGFloat) -> UIImage? {
        let bounds = FaceSwapOutlineValidation.boundsOf(outline.points)
        let padX = bounds.width * padding
        let padY = bounds.height * padding
        let normalized = CGRect(
            x: bounds.minX - padX,
            y: bounds.minY - padY,
            width: bounds.width + padX * 2,
            height: bounds.height + padY * 2
        )
        let pixel = CGRect(
            x: normalized.minX * CGFloat(raster.width),
            y: normalized.minY * CGFloat(raster.height),
            width: normalized.width * CGFloat(raster.width),
            height: normalized.height * CGFloat(raster.height)
        ).intersection(CGRect(x: 0, y: 0, width: raster.width, height: raster.height))
        let minX = max(0, Int(pixel.minX.rounded(.down)))
        let minY = max(0, Int(pixel.minY.rounded(.down)))
        let maxX = min(raster.width, Int(pixel.maxX.rounded(.up)))
        let maxY = min(raster.height, Int(pixel.maxY.rounded(.up)))
        let width = maxX - minX
        let height = maxY - minY
        guard width >= 8, height >= 8 else { return nil }
        var cropped = FaceSwapRaster.solid(width: width, height: height, red: 0, green: 0, blue: 0)
        for y in 0..<height {
            for x in 0..<width {
                guard let color = raster.rgb(x: minX + x, y: minY + y) else { continue }
                cropped.setRGB(x: x, y: y, red: color.0, green: color.1, blue: color.2)
            }
        }
        guard let image = cropped.uiImage() else { return nil }
        return FaceSwapRaster.decode(image, maxEdge: cropLongEdge)?.raster.uiImage() ?? image
    }
}

#if compiler(>=6.3) && canImport(FoundationModels)
@available(iOS 27.0, *)
private enum FaceSwapImageSession {
    static func findOutlines(preview: UIImage, request: String) async throws -> [FaceSwapOutline] {
        let session = LanguageModelSession(instructions: outlineInstructions)
        let response = try await session.respond(generating: FaceSwapOutlineSetFM.self) {
            """
            \(request)
            Trace only the faces this request names. Return closed skin contours, not a box, hair, or body.
            role is source for the appearance that should move, destination for the face that should change.
            Points are normalized, origin top-left, x and y from 0 to 1. Use 12 to 20 points.
            """
            Attachment(preview).label("preview")
        }
        let outlines = response.content.outlines.prefix(2).enumerated().compactMap { index, item -> FaceSwapOutline? in
            guard let role = FaceSwapRoleParser.role(from: item.role) else { return nil }
            let points = item.points.prefix(FaceSwapOutlineValidation.maximumPoints).map { point in
                CGPoint(x: point.x, y: point.y)
            }
            return FaceSwapOutline(
                id: "outline-\(index + 1)",
                role: role,
                refersTo: item.refersTo,
                points: points
            )
        }
        if outlines.isEmpty {
            throw FaceSwapImageError.emptyOutlines
        }
        return outlines
    }

    static func editPlan(
        request: String,
        outlines: [FaceSwapOutline],
        sourceCrop: UIImage,
        destinationCrop: UIImage
    ) async throws -> FaceSwapEditPlan {
        FaceSwapApplyRegionEditFMTool.lastPlan = nil
        let session = LanguageModelSession(tools: [FaceSwapApplyRegionEditFMTool()], instructions: editInstructions)
        let prompt = """
        \(request)

        \(FaceSwapOutlineValidation.promptBlock(outlines))

        The source crop is the appearance to transfer. The destination crop is the face that changes.
        Call applyRegionEdit once with a reconstruction recipe. Do not copy either crop onto the photo.
        """
        _ = try await session.respond {
            prompt
            Attachment(sourceCrop).label("source")
            Attachment(destinationCrop).label("destination")
        }
        guard let plan = FaceSwapApplyRegionEditFMTool.lastPlan else {
            throw FaceSwapImageError.missingEditPlan
        }
        FaceSwapApplyRegionEditFMTool.lastPlan = nil
        return plan
    }

    private static let outlineInstructions = """
    You trace face skin outlines. Return only the people the request names.
    Do not outline other people, hair, the body, or the frame. Do not return a rectangle.
    role is source or destination. Points are a closed contour, origin top-left, 0 to 1.
    """

    private static let editInstructions = """
    You choose a reconstruction inside an existing destination outline. Call applyRegionEdit once.
    Keep destination light and pose. Transfer source identity, not a copy of the source crop.
    fitPose reshapes onto the destination pose. lightingMatch places source color under destination light.
    detailTransfer adds source texture after relighting. inset and tightenedDestination can only shrink the write region.
    Then stop. Do not redraw the photo.
    """
}

@available(iOS 27.0, *)
@Generable
private struct FaceSwapOutlineSetFM {
    @Guide(description: "At most 2 face outlines named by the request")
    var outlines: [FaceSwapOutlineFM]
}

@available(iOS 27.0, *)
@Generable
private struct FaceSwapOutlineFM {
    @Guide(description: "source or destination")
    var role: String
    @Guide(description: "Phrase from the request, such as the man's face")
    var refersTo: String
    @Guide(description: "Closed face skin polygon, 12 to 20 points")
    var points: [FaceSwapOutlinePointFM]
}

@available(iOS 27.0, *)
@Generable
private struct FaceSwapOutlinePointFM {
    @Guide(description: "0 to 1, origin left")
    var x: Double
    @Guide(description: "0 to 1, origin top")
    var y: Double
}

@available(iOS 27.0, *)
private struct FaceSwapApplyRegionEditFMTool: Tool {
    nonisolated(unsafe) static var lastPlan: FaceSwapEditPlan?

    let name = "applyRegionEdit"
    let description = "Reconstruct inside the destination outline. Transfer identity under destination light. Cannot enlarge the outline or copy a crop."

    @Generable
    struct Arguments {
        @Guide(description: "0 to 1. Reshape the source face onto the destination pose")
        var fitPose: Double
        @Guide(description: "0.35 to 1. Place source color under destination light. Do not copy the crop")
        var lightingMatch: Double
        @Guide(description: "0 to 1. Pull color toward the destination face")
        var colorMatch: Double
        @Guide(description: "0 to 1. Add source texture after relighting. Not a crop copy")
        var detailTransfer: Double
        @Guide(description: "0.02 to 0.16. Inward seam width as a fraction of the face")
        var edgeBand: Double
        @Guide(description: "0 to 0.12. Shrinks the write region. Cannot enlarge it")
        var inset: Double
        @Guide(description: "One short reason this recipe fits the request")
        var motive: String
        @Guide(description: "0 to 16 points. Empty keeps the traced destination outline")
        var tightenedDestination: [FaceSwapOutlinePointFM]
    }

    func call(arguments: Arguments) async throws -> String {
        let tightened = arguments.tightenedDestination.prefix(FaceSwapOutlineValidation.maximumPoints).map { point in
            CGPoint(x: point.x, y: point.y)
        }
        let plan = FaceSwapEditPlan(
            fitPose: arguments.fitPose,
            lightingMatch: arguments.lightingMatch,
            colorMatch: arguments.colorMatch,
            detailTransfer: arguments.detailTransfer,
            edgeBand: arguments.edgeBand,
            inset: arguments.inset,
            motive: arguments.motive,
            tightenedDestination: tightened
        ).clamped()
        Self.lastPlan = plan
        let contour = plan.tightenedDestination.isEmpty ? "using the traced outline" : "using a tighter contour"
        return "Recorded reconstruction \(contour). Write region stays inside the destination outline."
    }
}
#endif

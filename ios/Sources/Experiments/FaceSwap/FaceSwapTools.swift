import Foundation
import UIKit

#if canImport(FoundationModels)
import FoundationModels
#endif

/// The on-device model chooses which tools to call. Tools write only inside catalog regions.
enum FaceSwapToolSession {
    static func run(request: String, raster: FaceSwapRaster) async throws -> FaceSwapScriptResult {
        let regions = FaceSwapRegions.detect(raster: raster)
        guard !regions.isEmpty else {
            throw FaceSwapOutlineFailure(message: "No faces or people were found in that photo.")
        }
        let commands = try await choose(request: request, regions: regions, raster: raster)
        guard !commands.isEmpty else {
            throw FaceSwapImageError.missingEditPlan
        }
        switch FaceSwapOperations.apply(commands: commands, regions: regions, original: raster) {
        case .success(let result):
            return result
        case .failure(let message):
            throw FaceSwapOutlineFailure(message: message)
        }
    }

    private static func choose(
        request: String,
        regions: [FaceSwapRegion],
        raster: FaceSwapRaster
    ) async throws -> [FaceSwapCommand] {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            return try await FaceSwapToolModel.choose(request: request, regions: regions, raster: raster)
        }
        #endif
        throw FaceSwapImageError.imageInputUnavailable
    }
}

final class FaceSwapEditBoard: @unchecked Sendable {
    static let shared = FaceSwapEditBoard()

    private let lock = NSLock()
    private var regions: [FaceSwapRegion] = []
    private var width = 0
    private var height = 0
    private var commands: [FaceSwapCommand] = []

    func begin(regions: [FaceSwapRegion], width: Int, height: Int) {
        lock.lock()
        self.regions = regions
        self.width = width
        self.height = height
        commands = []
        lock.unlock()
    }

    func record(_ command: FaceSwapCommand) -> String {
        lock.lock()
        defer { lock.unlock() }
        if commands.count >= 8 {
            return "Too many edits. Stop."
        }
        if let error = FaceSwapOperations.validate(command, regions: regions, width: width, height: height) {
            return error
        }
        commands.append(command)
        return "Recorded. The write stays inside the named region."
    }

    func finish() -> [FaceSwapCommand] {
        lock.lock()
        defer { lock.unlock() }
        let recorded = commands
        commands = []
        regions = []
        return recorded
    }
}

#if canImport(FoundationModels)
@available(iOS 26.0, *)
private enum FaceSwapToolModel {
    static func choose(
        request: String,
        regions: [FaceSwapRegion],
        raster: FaceSwapRaster
    ) async throws -> [FaceSwapCommand] {
        FaceSwapEditBoard.shared.begin(regions: regions, width: raster.width, height: raster.height)
        let session = LanguageModelSession(
            tools: [FaceSwapRemoveRegionTool(), FaceSwapCopyRegionTool(), FaceSwapReplaceFacesTool()],
            instructions: """
            You edit a photo only by calling tools. Do not redraw the photo.
            Use only listed region ids. A tool cannot grow a region or change pixels outside it.
            person color is clothing. A face with on= belongs to that person. Match "blue shirt" to color=blue, then use that face's id or the person's id.
            removeRegion erases one region by filling from nearby pixels.
            copyRegion adds copies at new centers. The original stays. Pass 4 centers to end up with 5.
            replaceFaces copies one face onto other face ids, inside those face contours only.
            Call the tools the request needs, then stop.
            """
        )
        let prompt = """
        \(request)

        \(FaceSwapRegions.catalog(regions))
        """
        if FaceSwapImagePromptSupport.canAttachImages, let preview = FaceSwapImagePrompt.previewImage(from: raster) {
            try await respondWithPreview(session: session, prompt: prompt, preview: preview)
        } else {
            _ = try await session.respond(to: prompt)
        }
        var commands = FaceSwapEditBoard.shared.finish()
        if commands.isEmpty {
            FaceSwapEditBoard.shared.begin(regions: regions, width: raster.width, height: raster.height)
            let retry = LanguageModelSession(
                tools: [FaceSwapRemoveRegionTool(), FaceSwapCopyRegionTool(), FaceSwapReplaceFacesTool()],
                instructions: "Call one of the edit tools using a listed region id. Then stop."
            )
            _ = try await retry.respond(to: "\(request)\nNo tool was called. Call a tool now.\n\(FaceSwapRegions.catalog(regions))")
            commands = FaceSwapEditBoard.shared.finish()
        }
        return commands
    }

    private static func respondWithPreview(
        session: LanguageModelSession,
        prompt: String,
        preview: UIImage
    ) async throws {
        #if compiler(>=6.3)
        if #available(iOS 27.0, *) {
            _ = try await session.respond {
                prompt
                Attachment(preview).label("photo")
            }
            return
        }
        #endif
        _ = try await session.respond(to: prompt)
    }
}

@available(iOS 26.0, *)
private struct FaceSwapRemoveRegionTool: Tool {
    let name = "removeRegion"
    let description = "Erase one listed region by filling from nearby pixels. Does not change pixels outside that region."

    @Generable
    struct Arguments {
        @Guide(description: "Region id from the list, such as person-1")
        var regionId: String
        @Guide(description: "0 to 0.12. Shrinks the erased area. Cannot enlarge it")
        var inset: Double
    }

    func call(arguments: Arguments) async throws -> String {
        FaceSwapEditBoard.shared.record(.remove(regionID: arguments.regionId, inset: arguments.inset))
    }
}

@available(iOS 26.0, *)
private struct FaceSwapCopyRegionTool: Tool {
    let name = "copyRegion"
    let description = "Add copies of one listed region at new centers. The original stays. Only the new copies are written."

    @Generable
    struct Arguments {
        @Guide(description: "Region id to copy, such as person-1")
        var sourceId: String
        @Guide(description: "1 to 6 new centers, normalized 0 to 1, origin top-left. For 5 total, pass 4 centers")
        var centers: [FaceSwapCenterFM]
    }

    func call(arguments: Arguments) async throws -> String {
        let centers = arguments.centers.prefix(FaceSwapOperations.maximumCopies).map { CGPoint(x: $0.x, y: $0.y) }
        return FaceSwapEditBoard.shared.record(.copy(sourceID: arguments.sourceId, centers: centers))
    }
}

@available(iOS 26.0, *)
private struct FaceSwapReplaceFacesTool: Tool {
    let name = "replaceFaces"
    let description = "Copy one face onto other face ids. Writes only inside those face contours. Does not copy a rectangle."

    @Generable
    struct Arguments {
        @Guide(description: "Face id whose appearance is copied, such as face-1")
        var sourceFaceId: String
        @Guide(description: "Face ids that change. Not the source id")
        var destinationFaceIds: [String]
        @Guide(description: "0 to 1. Reshape onto each destination pose")
        var fitPose: Double
        @Guide(description: "0.35 to 1. Place source color under destination light")
        var lightingMatch: Double
        @Guide(description: "0 to 1. Pull color toward each destination face")
        var colorMatch: Double
        @Guide(description: "0 to 1. Add source texture after relighting")
        var detailTransfer: Double
        @Guide(description: "0.02 to 0.16. Inward seam width")
        var edgeBand: Double
        @Guide(description: "0 to 0.12. Shrinks each write contour")
        var inset: Double
        @Guide(description: "One short reason this matches the request")
        var motive: String
    }

    func call(arguments: Arguments) async throws -> String {
        let plan = FaceSwapEditPlan(
            fitPose: arguments.fitPose,
            lightingMatch: arguments.lightingMatch,
            colorMatch: arguments.colorMatch,
            detailTransfer: arguments.detailTransfer,
            edgeBand: arguments.edgeBand,
            inset: arguments.inset,
            motive: arguments.motive,
            tightenedDestination: []
        ).clamped()
        return FaceSwapEditBoard.shared.record(
            .replaceFaces(
                sourceID: arguments.sourceFaceId,
                destinationIDs: Array(arguments.destinationFaceIds.prefix(FaceSwapOperations.maximumFaces)),
                plan: plan
            )
        )
    }
}

@available(iOS 26.0, *)
@Generable
private struct FaceSwapCenterFM {
    @Guide(description: "0 to 1, origin left")
    var x: Double
    @Guide(description: "0 to 1, origin top")
    var y: Double
}
#endif

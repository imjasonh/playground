import Foundation

struct FaceSwapTextDecision: Equatable, Sendable {
    var outlines: [FaceSwapOutline]
    var plan: FaceSwapEditPlan
}

enum FaceSwapTextPrompt {
    static func decide(request: String, raster: FaceSwapRaster) async throws -> FaceSwapTextDecision {
        let candidates = FaceSwapLandmarks.candidates(raster: raster)
        guard candidates.count >= 2 else {
            throw FaceSwapOutlineFailure(
                message: "Found \(candidates.count) face contour\(candidates.count == 1 ? "" : "s"). Need two faces in the photo."
            )
        }
        let choice = try await choose(request: request, candidates: candidates)
        switch FaceSwapContours.assign(
            sourceId: choice.sourceId,
            destinationId: choice.destinationId,
            sourcePhrase: choice.sourcePhrase,
            destinationPhrase: choice.destinationPhrase,
            candidates: candidates
        ) {
        case .success(let pair):
            return FaceSwapTextDecision(
                outlines: [pair.source, pair.destination],
                plan: choice.plan
            )
        case .failure(let message):
            let retry = try await choose(
                request: "\(request)\n\(message) Use only the listed ids.",
                candidates: candidates
            )
            switch FaceSwapContours.assign(
                sourceId: retry.sourceId,
                destinationId: retry.destinationId,
                sourcePhrase: retry.sourcePhrase,
                destinationPhrase: retry.destinationPhrase,
                candidates: candidates
            ) {
            case .success(let pair):
                return FaceSwapTextDecision(outlines: [pair.source, pair.destination], plan: retry.plan)
            case .failure(let retryMessage):
                throw FaceSwapOutlineFailure(message: retryMessage)
            }
        }
    }

    private static func choose(request: String, candidates: [FaceSwapCandidate]) async throws -> FaceSwapTextChoice {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            return try await FaceSwapTextSession.choose(request: request, candidates: candidates)
        }
        #endif
        throw FaceSwapImageError.imageInputUnavailable
    }
}

private struct FaceSwapTextChoice: Equatable {
    var sourceId: String
    var destinationId: String
    var sourcePhrase: String
    var destinationPhrase: String
    var plan: FaceSwapEditPlan
}

#if canImport(FoundationModels)
import FoundationModels

@available(iOS 26.0, *)
private enum FaceSwapTextSession {
    static func choose(request: String, candidates: [FaceSwapCandidate]) async throws -> FaceSwapTextChoice {
        let session = LanguageModelSession(instructions: """
            You choose which traced face contours a request names, then a reconstruction recipe.
            You cannot see the photo. Use only the listed ids. Do not invent points or a box.
            sourceId is the appearance to transfer. destinationId is the face that changes.
            Match place words in the request when they are present. chinContrast is lighting, not a person label.
            """)
        let prompt = """
            \(request)

            \(FaceSwapContours.catalog(candidates))

            Pick two different ids. Then choose how to reconstruct inside the destination contour.
            """
        let response = try await session.respond(to: prompt, generating: FaceSwapChoiceFM.self)
        let content = response.content
        return FaceSwapTextChoice(
            sourceId: content.sourceId,
            destinationId: content.destinationId,
            sourcePhrase: content.sourcePhrase,
            destinationPhrase: content.destinationPhrase,
            plan: FaceSwapEditPlan(
                fitPose: content.fitPose,
                lightingMatch: content.lightingMatch,
                colorMatch: content.colorMatch,
                detailTransfer: content.detailTransfer,
                edgeBand: content.edgeBand,
                inset: content.inset,
                motive: content.motive,
                tightenedDestination: []
            ).clamped()
        )
    }
}

@available(iOS 26.0, *)
@Generable
private struct FaceSwapChoiceFM {
    @Guide(description: "id of the face whose appearance moves")
    var sourceId: String
    @Guide(description: "id of the face that changes")
    var destinationId: String
    @Guide(description: "Phrase from the request for the source, such as the man's face")
    var sourcePhrase: String
    @Guide(description: "Phrase from the request for the destination")
    var destinationPhrase: String
    @Guide(description: "0 to 1. Reshape onto the destination pose")
    var fitPose: Double
    @Guide(description: "0.35 to 1. Place source color under destination light")
    var lightingMatch: Double
    @Guide(description: "0 to 1. Pull color toward the destination face")
    var colorMatch: Double
    @Guide(description: "0 to 1. Add source texture after relighting")
    var detailTransfer: Double
    @Guide(description: "0.02 to 0.16. Inward seam width")
    var edgeBand: Double
    @Guide(description: "0 to 0.12. Shrinks the write region")
    var inset: Double
    @Guide(description: "One short reason these ids and this recipe fit the request")
    var motive: String
}
#endif

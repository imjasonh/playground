import Foundation

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
        let chosen = try await choose(request: request, regions: regions, raster: raster)
        guard !chosen.commands.isEmpty else {
            throw FaceSwapImageError.missingEditPlan
        }
        switch FaceSwapOperations.apply(commands: chosen.commands, regions: regions, original: raster) {
        case .success(var result):
            result.log.insert(contentsOf: chosen.notes, at: 0)
            return result
        case .failure(let error):
            throw FaceSwapOutlineFailure(message: error.message)
        }
    }

    private static func choose(
        request: String,
        regions: [FaceSwapRegion],
        raster: FaceSwapRaster
    ) async throws -> FaceSwapModelChoice {
        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            return try await FaceSwapToolModel.choose(request: request, regions: regions, raster: raster)
        }
        #endif
        throw FaceSwapImageError.imageInputUnavailable
    }
}

struct FaceSwapModelChoice: Equatable, Sendable {
    var commands: [FaceSwapCommand]
    var notes: [String]
}

/// Sizes the one-shot prompt for the 4096-token on-device window (TN3193).
///
/// Tool schemas and the reply reserve stay out of the catalog. Overflow
/// recovery starts a new session with a shorter catalog, because the
/// overflowing content is the first turn itself.
enum FaceSwapModelBudget {
    static let toolsReserveTokens = 700
    static let imageReserveTokens = 900
    static let maxRequestChars = 280
    static let maxCatalogChars = 900
    static let minimumCatalogChars = 180
    static let retryCatalogChars = 420
    static let instructions = """
    You choose photo edits by calling tools. Use only listed region ids.
    Match clothing words to person color. A face with on= is that person's face.
    Do not redraw the photo. Then stop.
    """

    struct PromptPlan: Equatable {
        var prompt: String
        var attachPreview: Bool
    }

    static func plan(
        request: String,
        regions: [FaceSwapRegion],
        canAttachImages: Bool,
        hasPreview: Bool,
        includeImage: Bool,
        windowTokens: Int = AgentContextBudget.defaultWindowTokens,
        catalogCap: Int = maxCatalogChars
    ) -> PromptPlan {
        let cappedRequest = AgentContextBudget.truncateToChars(
            request.trimmingCharacters(in: .whitespacesAndNewlines),
            maxChars: maxRequestChars
        )
        var attach = includeImage && canAttachImages && hasPreview
        var available = availableCatalogChars(
            request: cappedRequest,
            attachPreview: attach,
            windowTokens: windowTokens
        )
        if attach, available < minimumCatalogChars {
            attach = false
            available = availableCatalogChars(
                request: cappedRequest,
                attachPreview: false,
                windowTokens: windowTokens
            )
        }
        let catalogChars = min(catalogCap, max(minimumCatalogChars, available))
        let catalog = FaceSwapRegions.catalog(regions, maxChars: catalogChars)
        return PromptPlan(
            prompt: promptText(request: cappedRequest, catalog: catalog, attachPreview: attach),
            attachPreview: attach
        )
    }

    /// Catalog characters that fit after instructions, tool schemas, the reply reserve, and an optional preview.
    static func availableCatalogChars(
        request: String,
        attachPreview: Bool,
        windowTokens: Int
    ) -> Int {
        let fixed = AgentContextBudget.estimateTokens(instructions)
            + toolsReserveTokens
            + AgentContextBudget.responseReserveTokens
            + (attachPreview ? imageReserveTokens : 0)
            + AgentContextBudget.estimateTokens(request)
            + 48
        let room = max(0, windowTokens - fixed)
        return AgentContextBudget.maxChars(forTokens: room)
    }

    static func promptText(request: String, catalog: String, attachPreview: Bool) -> String {
        let task = attachPreview
            ? "Use the attached photo only to match listed ids. Call the tools this request needs, then stop."
            : "Match listed ids. Call the tools this request needs, then stop."
        return """
        \(request)

        \(catalog)

        \(task)
        """
    }
}

enum FaceSwapModelLimits {
    static func failure(_ error: Error) -> Error {
        if OnDeviceContextManager.isExceededContextWindow(error) {
            return FaceSwapModelLimitError.contextExceeded
        }
        let text = "\(error.localizedDescription) \(String(describing: error))".lowercased()
        if text.contains("guardrail") || text.contains("refusal") || text.contains("refused") {
            return FaceSwapModelLimitError.refused
        }
        if text.contains("unsupportedlanguage") || text.contains("unsupported language") {
            return FaceSwapModelLimitError.unsupportedLanguage
        }
        return error
    }
}

enum FaceSwapModelLimitError: LocalizedError, Equatable {
    case contextExceeded
    case refused
    case unsupportedLanguage

    var errorDescription: String? {
        switch self {
        case .contextExceeded:
            return "The on-device model ran out of context. Shorten the request and try again."
        case .refused:
            return "The on-device model refused that request. No pixels changed."
        case .unsupportedLanguage:
            return "The on-device model does not support that language. Try the request in English."
        }
    }
}

final class FaceSwapEditBoard: @unchecked Sendable {
    static let shared = FaceSwapEditBoard()
    static let maximumCommands = 4

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
        if commands.count >= Self.maximumCommands {
            return capped("Stop. Enough edits.")
        }
        if let error = FaceSwapOperations.validate(command, regions: regions, width: width, height: height) {
            return capped(error)
        }
        commands.append(command)
        return capped("Recorded.")
    }

    func finish() -> [FaceSwapCommand] {
        lock.lock()
        defer { lock.unlock() }
        let recorded = commands
        commands = []
        regions = []
        return recorded
    }

    private func capped(_ text: String) -> String {
        AgentContextBudget.truncateToChars(text, maxChars: 160)
    }
}

#if canImport(FoundationModels)
@available(iOS 26.0, *)
private enum FaceSwapToolModel {
    static func choose(
        request: String,
        regions: [FaceSwapRegion],
        raster: FaceSwapRaster
    ) async throws -> FaceSwapModelChoice {
        let window = windowTokens()
        let first = FaceSwapModelBudget.plan(
            request: request,
            regions: regions,
            canAttachImages: FaceSwapImagePromptSupport.canAttachImages,
            hasPreview: false,
            includeImage: false,
            windowTokens: window
        )
        do {
            let commands = try await respond(
                plan: first,
                regions: regions,
                raster: raster,
                instructions: FaceSwapModelBudget.instructions
            )
            if commands.isEmpty {
                let textOnly = FaceSwapModelBudget.plan(
                    request: request,
                    regions: regions,
                    canAttachImages: false,
                    hasPreview: false,
                    includeImage: false,
                    windowTokens: window
                )
                let retryCommands = try await respond(
                    plan: textOnly,
                    regions: regions,
                    raster: raster,
                    instructions: "Call one listed tool now. Then stop."
                )
                return FaceSwapModelChoice(commands: retryCommands, notes: [])
            }
            return FaceSwapModelChoice(commands: commands, notes: [])
        } catch {
            guard OnDeviceContextManager.isExceededContextWindow(error) else {
                throw FaceSwapModelLimits.failure(error)
            }
        }
        let smaller = FaceSwapModelBudget.plan(
            request: request,
            regions: regions,
            canAttachImages: false,
            hasPreview: false,
            includeImage: false,
            windowTokens: window,
            catalogCap: FaceSwapModelBudget.retryCatalogChars
        )
        do {
            let commands = try await respond(
                plan: smaller,
                regions: regions,
                raster: raster,
                instructions: FaceSwapModelBudget.instructions
            )
            return FaceSwapModelChoice(
                commands: commands,
                notes: ["Context was full. Retried with a shorter catalog."]
            )
        } catch {
            if OnDeviceContextManager.isExceededContextWindow(error) {
                throw FaceSwapModelLimitError.contextExceeded
            }
            throw FaceSwapModelLimits.failure(error)
        }
    }

    private static func respond(
        plan: FaceSwapModelBudget.PromptPlan,
        regions: [FaceSwapRegion],
        raster: FaceSwapRaster,
        instructions: String
    ) async throws -> [FaceSwapCommand] {
        FaceSwapEditBoard.shared.begin(regions: regions, width: raster.width, height: raster.height)
        let session = LanguageModelSession(
            tools: [FaceSwapRemoveRegionTool(), FaceSwapCopyRegionTool(), FaceSwapReplaceFacesTool()],
            instructions: instructions
        )
        session.prewarm()
        _ = try await session.respond(to: plan.prompt)
        return FaceSwapEditBoard.shared.finish()
    }

    /// `contextSize` is on newer SDKs. Fall back to the documented 4096-token window.
    private static func windowTokens() -> Int {
        let mirror = Mirror(reflecting: SystemLanguageModel.default)
        for child in mirror.children {
            if child.label == "contextSize", let value = child.value as? Int, value > 0 {
                return value
            }
        }
        return AgentContextBudget.defaultWindowTokens
    }
}

@available(iOS 26.0, *)
private struct FaceSwapRemoveRegionTool: Tool {
    let name = "removeRegion"
    let description = "Erase one listed region. Pixels outside it stay unchanged."

    @Generable
    struct Arguments {
        @Guide(description: "Listed id")
        var regionId: String
    }

    func call(arguments: Arguments) async throws -> String {
        FaceSwapEditBoard.shared.record(.remove(regionID: arguments.regionId, inset: 0))
    }
}

@available(iOS 26.0, *)
private struct FaceSwapCopyRegionTool: Tool {
    let name = "copyRegion"
    let description = "Add copies of one listed region. The original stays."

    @Generable
    struct Arguments {
        @Guide(description: "Listed id")
        var sourceId: String
        @Guide(.maximumCount(6))
        @Guide(description: "New centers, 0 to 1, origin top-left. Four centers make five total")
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
    let description = "Copy one face onto other face ids, inside those contours only."

    @Generable
    struct Arguments {
        @Guide(description: "Face id to copy")
        var sourceFaceId: String
        @Guide(.minimumCount(1), .maximumCount(8))
        @Guide(description: "Face ids that change")
        var destinationFaceIds: [String]
    }

    func call(arguments: Arguments) async throws -> String {
        return FaceSwapEditBoard.shared.record(
            .replaceFaces(
                sourceID: arguments.sourceFaceId,
                destinationIDs: Array(arguments.destinationFaceIds.prefix(FaceSwapOperations.maximumFaces)),
                plan: FaceSwapEditPlan.identity.clamped()
            )
        )
    }
}

@available(iOS 26.0, *)
@Generable
private struct FaceSwapCenterFM {
    var x: Double
    var y: Double
}
#endif

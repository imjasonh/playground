import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// User-facing copy when on-device triage fails mid-turn.
enum TriageFailureMessage {
    static let generic = """
        Apple Intelligence couldn’t finish this reply. Tap New chat and try again, \
        or use the Toolbox tab to run checks yourself.
        """

    /// Prefer a concrete recovery hint over Apple’s opaque
    /// `GenerationError error -1` localizedDescription.
    static func from(_ error: Error) -> String {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), let mapped = mapGenerationError(error) {
            return mapped
        }
        #endif
        let ns = error as NSError
        if ns.domain.localizedCaseInsensitiveContains("FoundationModels")
            || ns.domain.localizedCaseInsensitiveContains("GenerationError")
            || ns.localizedDescription.localizedCaseInsensitiveContains("GenerationError")
        {
            return generic
        }
        let detail = error.localizedDescription.trimmingCharacters(in: .whitespacesAndNewlines)
        if detail.isEmpty || detail == "The operation couldn’t be completed." {
            return generic
        }
        // Still avoid dumping raw domain/code strings as the whole message.
        if detail.contains("GenerationError") || detail.contains("error -1") {
            return generic
        }
        return """
            Apple Intelligence couldn’t finish this reply (\(detail)). Tap New chat \
            and try again, or use the Toolbox tab.
            """
    }

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    private static func mapGenerationError(_ error: Error) -> String? {
        guard let generation = error as? LanguageModelSession.GenerationError else {
            return nil
        }
        switch generation {
        case .exceededContextWindowSize:
            return """
                This chat ran out of room for Apple Intelligence. Tap New chat and \
                ask again (shorter is better).
                """
        case .assetsUnavailable:
            return """
                Apple Intelligence model assets aren’t ready. Open Settings to check \
                Apple Intelligence, wait for downloads to finish, then tap New chat — \
                or use the Toolbox tab.
                """
        case .rateLimited:
            return """
                Apple Intelligence is temporarily rate-limited. Wait a moment and try \
                again, or use the Toolbox tab.
                """
        case .guardrailViolation:
            return """
                Apple Intelligence blocked that prompt or reply. Rephrase the question, \
                or use the Toolbox tab for manual checks.
                """
        case .refusal:
            return """
                Apple Intelligence declined to answer. Try rephrasing, or use the \
                Toolbox tab.
                """
        case .unsupportedLanguageOrLocale:
            return """
                Apple Intelligence doesn’t support this language for triage yet. Try \
                English, or use the Toolbox tab.
                """
        default:
            // decodingFailure / unsupportedGuide / unknown codes (incl. error -1)
            return generic
        }
    }
    #endif
}

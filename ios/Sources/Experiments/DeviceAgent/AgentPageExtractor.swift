import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

/// Turns a browser scrape into short, question-relevant bullets via Foundation Models.
/// No heuristic fallback. Extraction failures surface so we can fix the model path.
enum AgentPageExtractor {
    struct Input: Equatable {
        var userQuestion: String
        var title: String
        var url: String
        var headings: [String]
        var listItems: [String]
        var pageText: String
    }

    enum ExtractionError: Error, LocalizedError, Equatable {
        case modelUnavailable
        case emptyFindings(rawBulletCount: Int)
        case modelFailed(String)

        var code: String {
            switch self {
            case .modelUnavailable: return "modelUnavailable"
            case .emptyFindings: return "emptyFindings"
            case .modelFailed: return "modelFailed"
            }
        }

        var errorDescription: String? {
            switch self {
            case .modelUnavailable:
                return "Foundation Models isn’t available to extract page findings."
            case .emptyFindings(let count):
                return "Foundation Models returned no usable page findings (raw bullets: \(count))."
            case .modelFailed(let message):
                return "Foundation Models page extraction failed: \(message)"
            }
        }
    }

    /// Failed extraction with the raw model output when available (for dump diagnostics).
    struct Failure: Error, LocalizedError {
        var error: ExtractionError
        var rawModelBullets: [String]?

        var errorDescription: String? { error.errorDescription }
        var code: String { error.code }
    }

    /// Test hook: when set, skips the live model. Return bullets or throw.
    static var testExtractionOverride: ((Input) throws -> [String])?

    static func extract(from input: Input) async throws -> [String] {
        if let override = testExtractionOverride {
            return try sanitizeBullets(try override(input))
        }

        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            return try await foundationModelBullets(from: input)
        }
        #endif
        throw Failure(error: .modelUnavailable)
    }

    static func formatFindings(title: String, url: String, bullets: [String]) -> String {
        var lines: [String] = []
        let heading = title.trimmingCharacters(in: .whitespacesAndNewlines)
        if !heading.isEmpty {
            lines.append("From the page · \(heading)")
        } else if !url.isEmpty {
            lines.append("From the page · \(url)")
        } else {
            lines.append("From the page")
        }
        lines.append(contentsOf: bullets.map { "• \($0)" })
        lines.append("Ask a follow-up to dig into this same browser tab.")
        return lines.joined(separator: "\n")
    }

    static func formatExtractionFailure(
        title: String,
        url: String,
        error: Error,
        approximateBullets: [String] = []
    ) -> String {
        var lines: [String] = []
        let heading = title.trimmingCharacters(in: .whitespacesAndNewlines)
        if !heading.isEmpty {
            lines.append("Page extraction failed · \(heading)")
        } else if !url.isEmpty {
            lines.append("Page extraction failed · \(url)")
        } else {
            lines.append("Page extraction failed")
        }
        lines.append(error.localizedDescription)
        if !approximateBullets.isEmpty {
            lines.append("Approximate findings from the scrape:")
            lines.append(contentsOf: approximateBullets.map { "• \($0)" })
        } else {
            lines.append(
                "Dismiss cookie or sign-in chrome, scroll to the content, then Ask a follow-up."
            )
        }
        lines.append("Export the conversation ZIP for diagnostics.")
        return lines.joined(separator: "\n")
    }

    static func sanitizeBullets(_ bullets: [String], limit: Int = 8) throws -> [String] {
        var out: [String] = []
        for raw in bullets {
            let chunk = raw
                .replacingOccurrences(of: #"\s+"#, with: " ", options: .regularExpression)
                .trimmingCharacters(in: .whitespacesAndNewlines)
            guard chunk.count >= 4, chunk.count <= 160 else { continue }
            let lower = chunk.lowercased()
            if AgentBrowserSession.isChromeNoise(lower) { continue }
            let key = String(lower.prefix(36))
            if out.contains(where: { $0.lowercased().hasPrefix(key) }) { continue }
            out.append(chunk)
            if out.count >= limit { break }
        }
        guard !out.isEmpty else {
            throw Failure(
                error: .emptyFindings(rawBulletCount: bullets.count),
                rawModelBullets: bullets
            )
        }
        return out
    }

    static func buildPrompt(from input: Input) -> String {
        var sections: [String] = [
            "User question:",
            input.userQuestion.isEmpty ? "(none)" : input.userQuestion,
            "",
            "Page title: \(input.title.isEmpty ? "(none)" : input.title)",
            "Page URL: \(input.url.isEmpty ? "(none)" : input.url)",
        ]
        if !input.headings.isEmpty {
            sections.append("Headings:")
            sections.append(contentsOf: input.headings.prefix(12).map { "- \($0)" })
        }
        if !input.listItems.isEmpty {
            sections.append("List items:")
            sections.append(contentsOf: input.listItems.prefix(24).map { "- \($0)" })
        }
        // Keep extraction prompts well under the 4096-token window.
        let text = String(input.pageText.prefix(2_000))
        if !text.isEmpty {
            sections.append("Page text:")
            sections.append(text)
        }
        sections.append("")
        sections.append(
            "Extract 3-8 short factual bullets from the page that answer the user question. Use only page content."
        )
        return sections.joined(separator: "\n")
    }

    static func unpackError(_ error: Error) -> (code: String, message: String, rawBullets: [String]?) {
        if let failure = error as? Failure {
            return (failure.code, failure.localizedDescription, failure.rawModelBullets)
        }
        if let extraction = error as? ExtractionError {
            return (extraction.code, extraction.localizedDescription, nil)
        }
        return ("modelFailed", error.localizedDescription, nil)
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    @Generable
    struct ModelFindings {
        @Guide(description: "3-8 short factual bullets from the page that answer the user question")
        var bullets: [String]
    }

    @available(iOS 26.0, *)
    private static func foundationModelBullets(from input: Input) async throws -> [String] {
        let model = SystemLanguageModel.default
        guard model.isAvailable else {
            throw Failure(error: .modelUnavailable)
        }

        let session = LanguageModelSession(instructions: """
            You extract facts from a scraped web page for Device Agent.
            Return only short bullets grounded in the page headings, list items, and text.
            Prefer schedules, scores, names, dates, and numbers that answer the user question.
            Do not summarize the chat. Do not invent facts. Skip nav, cookies, and login chrome.
            """)
        let prompt = buildPrompt(from: input)
        do {
            let response = try await session.respond(to: prompt, generating: ModelFindings.self)
            return try sanitizeBullets(response.content.bullets)
        } catch let failure as Failure {
            throw failure
        } catch {
            throw Failure(error: .modelFailed(error.localizedDescription))
        }
    }
    #endif
}

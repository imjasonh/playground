import Foundation

#if canImport(FoundationModels)
import FoundationModels
#endif

/// Turns a browser scrape into short, question-relevant bullets via Foundation Models.
/// Falls back to structural heuristics when the model is unavailable or fails.
enum AgentPageExtractor {
    struct Input: Equatable {
        var userQuestion: String
        var title: String
        var url: String
        var headings: [String]
        var listItems: [String]
        var pageText: String
    }

    /// Test hook: when set, skips the live model and returns these bullets (or `nil` to use heuristic).
    static var testBulletsOverride: ((Input) -> [String]?)?

    static func extract(from input: Input) async -> [String] {
        if let override = testBulletsOverride {
            if let bullets = override(input) {
                return sanitizeBullets(bullets)
            }
            return heuristicBullets(from: input)
        }

        #if canImport(FoundationModels)
        if #available(iOS 26.0, *) {
            if let bullets = await foundationModelBullets(from: input), !bullets.isEmpty {
                return sanitizeBullets(bullets)
            }
        }
        #endif
        return heuristicBullets(from: input)
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
        if bullets.isEmpty {
            lines.append("• (No readable page content scraped — try another page or click into the content.)")
        } else {
            lines.append(contentsOf: bullets.map { "• \($0)" })
        }
        lines.append("Ask a follow-up to dig into this same browser tab.")
        return lines.joined(separator: "\n")
    }

    static func heuristicBullets(from input: Input, limit: Int = 8) -> [String] {
        AgentBrowserSession.pageFindingsBullets(
            headings: input.headings,
            listItems: input.listItems,
            pageText: input.pageText,
            limit: limit
        )
    }

    static func sanitizeBullets(_ bullets: [String], limit: Int = 8) -> [String] {
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
        let text = String(input.pageText.prefix(3500))
        if !text.isEmpty {
            sections.append("Page text:")
            sections.append(text)
        }
        sections.append("")
        sections.append(
            "Extract 3–8 short factual bullets from the page that answer the user question. Use only page content."
        )
        return sections.joined(separator: "\n")
    }

    #if canImport(FoundationModels)
    @available(iOS 26.0, *)
    @Generable
    struct ModelFindings {
        @Guide(description: "3–8 short factual bullets from the page that answer the user question")
        var bullets: [String]
    }

    @available(iOS 26.0, *)
    private static func foundationModelBullets(from input: Input) async -> [String]? {
        let model = SystemLanguageModel.default
        guard model.isAvailable else { return nil }

        let session = LanguageModelSession(instructions: """
            You extract facts from a scraped web page for Device Agent.
            Return only short bullets grounded in the page headings, list items, and text.
            Prefer schedules, scores, names, dates, and numbers that answer the user question.
            Do not summarize the chat. Do not invent facts. Skip nav, cookies, and login chrome.
            """)
        let prompt = buildPrompt(from: input)
        do {
            let response = try await session.respond(to: prompt, generating: ModelFindings.self)
            return response.content.bullets
        } catch {
            // Fall back to a plain-text pass if guided generation fails on this OS build.
            do {
                let response = try await session.respond(to: prompt)
                return bulletsFromPlainText(response.content)
            } catch {
                return nil
            }
        }
    }

    private static func bulletsFromPlainText(_ text: String) -> [String] {
        text
            .components(separatedBy: .newlines)
            .map {
                $0.trimmingCharacters(in: .whitespacesAndNewlines)
                    .replacingOccurrences(of: #"^[-•*]\s*"#, with: "", options: .regularExpression)
            }
            .filter { !$0.isEmpty }
    }
    #endif
}

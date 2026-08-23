import Foundation

/// Plans tool calls when Apple Intelligence / Foundation Models is unavailable.
enum AgentFallbackPlanner {
    struct Step {
        var tool: String
        var args: [String: String]
    }

    static func steps(for prompt: String, mode: AgentMode) -> (steps: [Step], coda: String) {
        let lower = prompt.lowercased()
        var steps: [Step] = []

        if lower.contains("help") || lower.contains("what can you") {
            return ([], AgentToolExecutor.helpText(mode: mode))
        }
        if lower.contains("attachment") || lower.contains("inbox") || lower.contains("file") {
            steps.append(Step(tool: "listAttachments", args: [:]))
            if let name = extractAfter(keywords: ["read ", "open ", "summarize "], in: lower) {
                steps.append(Step(tool: "readTextAttachment", args: ["filenameQuery": name]))
            }
        }
        if lower.contains("contact") || lower.contains("mom") || lower.contains("dad")
            || lower.contains("who is") || lower.contains("phone for") || lower.contains("email for") {
            let query: String
            if lower.contains("mom") { query = "mom" }
            else if lower.contains("dad") { query = "dad" }
            else { query = extractNameQuery(from: prompt) ?? prompt }
            steps.append(Step(tool: "searchContacts", args: ["query": query]))
        }
        if lower.contains("where am i") || lower.contains("my location") || lower.contains("gps") {
            steps.append(Step(tool: "getCurrentLocation", args: [:]))
        }
        if lower.contains("direction") || lower.contains("maps") || lower.contains("navigate to") {
            let dest = extractAfter(keywords: ["to ", "toward ", "towards "], in: prompt)
                ?? extractAfter(keywords: ["directions "], in: prompt)
                ?? "home"
            steps.append(Step(tool: "openMapsDirections", args: ["query": dest]))
        }
        if lower.contains("calendar") || lower.contains("schedule") || lower.contains("add event") {
            let title = extractQuoted(from: prompt) ?? "Device Agent event"
            steps.append(Step(
                tool: "createCalendarEvent",
                args: ["title": title, "notes": prompt, "hoursFromNow": "2"]
            ))
        }
        if lower.contains("text ") || lower.contains("sms") || lower.contains("imessage") {
            steps.append(Step(
                tool: "draftSMS",
                args: ["recipients": "555", "body": prompt]
            ))
        }
        if lower.contains("email") || lower.contains("mail ") {
            steps.append(Step(
                tool: "draftEmail",
                args: [
                    "to": "someone@example.com",
                    "subject": extractQuoted(from: prompt) ?? "Hello",
                    "body": prompt,
                ]
            ))
        }
        if lower.contains("browser") || lower.contains("demo mail") || lower.contains("webview") {
            steps.append(Step(tool: "browserLoadDemo", args: [:]))
            steps.append(Step(tool: "browserRead", args: [:]))
        }
        if lower.contains("time") || lower.contains("date") || lower.contains("today") {
            steps.append(Step(tool: "getCurrentDateTime", args: [:]))
        }
        if lower.hasPrefix("http://") || lower.hasPrefix("https://") {
            steps.append(Step(tool: "openURL", args: ["url": prompt.trimmingCharacters(in: .whitespacesAndNewlines)]))
        }

        if steps.isEmpty {
            return ([], """
                I could not map that to a tool without Apple Intelligence. Try: list attachments, \
                find contact Mom, where am I, directions to …, schedule “Title”, demo mail, or help.
                """)
        }
        return (steps, "Finished planned tools (fallback planner — enable Apple Intelligence for richer routing).")
    }

    private static func extractQuoted(from prompt: String) -> String? {
        guard let first = prompt.firstIndex(of: "\""),
              let second = prompt[prompt.index(after: first)...].firstIndex(of: "\"") else {
            return nil
        }
        return String(prompt[prompt.index(after: first)..<second])
    }

    private static func extractAfter(keywords: [String], in prompt: String) -> String? {
        let lower = prompt.lowercased()
        for key in keywords {
            if let range = lower.range(of: key) {
                let rest = prompt[range.upperBound...].trimmingCharacters(in: .whitespacesAndNewlines)
                if !rest.isEmpty { return String(rest.prefix(80)) }
            }
        }
        return nil
    }

    private static func extractNameQuery(from prompt: String) -> String? {
        let patterns = ["contact ", "find ", "look up ", "lookup ", "phone for ", "email for ", "who is "]
        return extractAfter(keywords: patterns, in: prompt)
    }
}

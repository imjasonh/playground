import Foundation

/// Maps raw tool / navigation / model errors into short, actionable chat copy.
enum AgentErrorCopy {
    /// User-visible message for a failed agent turn.
    static func userMessage(for error: Error) -> String {
        if let tool = error as? AgentToolError {
            return message(for: tool)
        }
        let ns = error as NSError
        if ns.domain == NSURLErrorDomain {
            return networkMessage(code: ns.code, fallback: error.localizedDescription)
        }
        let text = error.localizedDescription
        let lower = text.lowercased()
        if lower.contains("timed out loading") || lower.contains("timeout") {
            return "That page took too long to load. Try a simpler URL, or Ask again after the tab finishes."
        }
        if lower.contains("bridge is not available") {
            return "The in-app browser couldn’t talk to that page (often a blank or blocked document). Open a normal http(s) page and try again."
        }
        if AgentRuntime.isExceededContextWindow(error) {
            return "The on-device model ran out of context. Device Agent compacted the session — Ask again to continue on the open tab."
        }
        if lower.contains("page extraction") || lower.contains("empty findings") {
            return """
            Page extraction didn’t return usable facts. \
            Dismiss cookie/sign-in chrome, scroll to the content, then Ask a follow-up — \
            or export the conversation ZIP to inspect the scrape.
            """
            .replacingOccurrences(of: "\n", with: " ")
        }
        if text.count > 220 {
            return String(text.prefix(200)) + "…"
        }
        return text
    }

    static func message(for error: AgentToolError) -> String {
        switch error {
        case .permissionDenied, .permissionNeeded, .cancelled:
            return error.localizedDescription
        case .invalidArguments(let message):
            return message
        case .unavailable(let message):
            let lower = message.lowercased()
            if lower.contains("timed out loading") {
                return "That page took too long to load. Try a simpler URL, or Ask again after the tab finishes."
            }
            if lower.hasPrefix("browser click") || lower.hasPrefix("browser clicktext") {
                return "\(message). Call browserFind or browserSnapshot for a fresh control list, then try again."
            }
            if lower.hasPrefix("browser type") || lower.hasPrefix("browser select") {
                return "\(message). Snapshot or find the control again before typing or selecting."
            }
            if lower.contains("need an absolute http") {
                return "Open a full http(s) URL (including https://)."
            }
            return message
        }
    }

    private static func networkMessage(code: Int, fallback: String) -> String {
        switch code {
        case NSURLErrorNotConnectedToInternet, NSURLErrorNetworkConnectionLost:
            return "No network connection. Check Wi‑Fi or cellular, then Ask again."
        case NSURLErrorTimedOut:
            return "The page timed out. Try again, or open a lighter URL."
        case NSURLErrorCannotFindHost, NSURLErrorDNSLookupFailed:
            return "Couldn’t find that host. Check the URL spelling and try again."
        case NSURLErrorAppTransportSecurityRequiresSecureConnection:
            return "Only http(s) pages that meet App Transport Security can load here."
        case NSURLErrorCancelled:
            return "Page load was cancelled."
        default:
            if fallback.count > 220 {
                return String(fallback.prefix(200)) + "…"
            }
            return fallback.isEmpty ? "Couldn’t load that page." : fallback
        }
    }
}

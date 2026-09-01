import Foundation

/// Shared mutable state browser tools read and write.
@MainActor
final class AgentToolContext: ObservableObject {
    let permissions: AgentPermissionGate
    let browser: AgentBrowserSession

    @Published var browserURL: URL?
    @Published var browserTitle: String = ""
    @Published var lastToolLog: [(name: String, detail: String)] = []

    init() {
        self.permissions = AgentPermissionGate.shared
        self.browser = AgentBrowserSession.shared
    }

    init(permissions: AgentPermissionGate) {
        self.permissions = permissions
        self.browser = AgentBrowserSession.shared
    }

    init(permissions: AgentPermissionGate, browser: AgentBrowserSession) {
        self.permissions = permissions
        self.browser = browser
    }

    func logTool(name: String, detail: String) {
        lastToolLog.append((name, detail))
        if lastToolLog.count > 50 {
            lastToolLog.removeFirst(lastToolLog.count - 50)
        }
    }
}

/// Concrete browser tool implementations used by Foundation Models tool wrappers.
@MainActor
enum AgentToolExecutor {
    static func getCurrentDateTime() -> String {
        let formatter = DateFormatter()
        formatter.dateStyle = .full
        formatter.timeStyle = .medium
        return formatter.string(from: Date())
    }

    static func browserOpen(context: AgentToolContext, urlString: String) async throws -> String {
        let trimmed = urlString.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let url = URL(string: trimmed),
              let scheme = url.scheme?.lowercased(),
              scheme == "http" || scheme == "https",
              url.host != nil
        else {
            throw AgentToolError.invalidArguments("Need an absolute http(s) URL with a host.")
        }
        try await context.browser.open(url)
        context.browserURL = context.browser.url ?? url
        context.browserTitle = context.browser.title
        context.logTool(name: "browserOpen", detail: url.absoluteString)
        return "Loaded \(context.browser.url?.absoluteString ?? url.absoluteString) in the in-app browser. Call browserSnapshot next."
    }

    static func browserRead(context: AgentToolContext) -> String {
        context.browserURL = context.browser.url ?? context.browserURL
        context.browserTitle = context.browser.title.isEmpty ? context.browserTitle : context.browser.title
        return context.browser.statusSummary()
    }

    static func browserSnapshot(context: AgentToolContext, maxTextChars: Double) async throws -> String {
        let chars = Int(maxTextChars.rounded())
        let snap = try await context.browser.snapshot(
            maxTextChars: chars > 0 ? chars : AgentContextBudget.defaultSnapshotTextChars
        )
        context.browserURL = context.browser.url ?? context.browserURL
        context.browserTitle = context.browser.title
        context.logTool(name: "browserSnapshot", detail: "\(snap.count) chars")
        return snap
    }

    static func browserClick(context: AgentToolContext, ref: String) async throws -> String {
        let result = try await context.browser.click(ref: ref)
        context.logTool(name: "browserClick", detail: ref)
        return result
    }

    static func browserType(
        context: AgentToolContext,
        ref: String,
        text: String,
        submit: Bool
    ) async throws -> String {
        let result = try await context.browser.type(ref: ref, text: text, submit: submit)
        context.logTool(name: "browserType", detail: "\(ref) submit=\(submit)")
        return result
    }

    static func browserBack(context: AgentToolContext) async throws -> String {
        let result = try await context.browser.goBack()
        context.browserURL = context.browser.url
        context.browserTitle = context.browser.title
        context.logTool(name: "browserBack", detail: context.browser.url?.absoluteString ?? "")
        return result
    }

    static func helpText() -> String {
        """
        Device Agent drives an in-app browser with the on-device Foundation Model. \
        Ask it to open an http(s) URL, then it snapshots the page, extracts answer bullets, \
        and can click or type by element ref. The tab stays open for follow-ups. \
        Requires Apple Intelligence on this device.
        """
    }
}

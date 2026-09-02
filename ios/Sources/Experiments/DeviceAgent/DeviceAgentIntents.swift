import AppIntents
import Foundation
import SwiftUI

/// Shared enqueue + navigation used by Device Agent App Intents.
@MainActor
enum DeviceAgentIntentActions {
    static func ask(prompt: String, preferVoice: Bool = false) -> String {
        AgentInbox.shared.enqueue(
            prompt: prompt,
            source: .shortcut,
            preferVoice: preferVoice
        )
        PlaygroundRouter.shared.openDeviceAgent()
        return "Queued for Device Agent."
    }

    static func browse(url: URL, prompt: String = "", preferVoice: Bool = false) throws -> String {
        guard let scheme = url.scheme?.lowercased(),
              scheme == "http" || scheme == "https",
              url.host != nil
        else {
            throw DeviceAgentIntentError.invalidURL
        }
        AgentInbox.shared.enqueueBrowserDrive(
            url: url,
            prompt: prompt,
            source: .shortcut,
            preferVoice: preferVoice
        )
        PlaygroundRouter.shared.openDeviceAgent()
        if prompt.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            return "Opening \(url.absoluteString) in Device Agent."
        }
        return "Opening \(url.absoluteString) in Device Agent with your prompt."
    }
}

enum DeviceAgentIntentError: Error, CustomLocalizedStringResourceConvertible {
    case invalidURL
    case emptyQuery

    var localizedStringResource: LocalizedStringResource {
        switch self {
        case .invalidURL:
            return "Device Agent needs an absolute http(s) URL with a host."
        case .emptyQuery:
            return "Device Agent needs a non-empty search query."
        }
    }
}

/// Shortcut / Siri entry: queue a free-form prompt, then open Device Agent.
struct AskDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Ask Device Agent"
    static var description = IntentDescription(
        "Queues a Device Agent prompt and opens Playground so the on-device model can drive the in-app browser."
    )
    static var openAppWhenRun = true

    @Parameter(title: "Prompt")
    var prompt: String

    @Parameter(title: "Prefer Voice", default: false)
    var preferVoice: Bool

    static var parameterSummary: some ParameterSummary {
        Summary("Ask Device Agent \(\.$prompt)") {
            \.$preferVoice
        }
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        let message = DeviceAgentIntentActions.ask(prompt: prompt, preferVoice: preferVoice)
        return .result(value: message, dialog: IntentDialog(stringLiteral: message))
    }
}

/// Opens an http(s) URL in Device Agent’s in-app browser, then runs a prompt.
struct BrowseURLWithDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Browse URL with Device Agent"
    static var description = IntentDescription(
        "Opens a web page in Device Agent’s in-app browser and lets the on-device model drive it."
    )
    static var openAppWhenRun = true

    @Parameter(title: "URL")
    var url: URL

    @Parameter(title: "Prompt")
    var prompt: String?

    static var parameterSummary: some ParameterSummary {
        Summary("Browse \(\.$url) with Device Agent") {
            \.$prompt
        }
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        let message = try DeviceAgentIntentActions.browse(url: url, prompt: prompt ?? "")
        return .result(value: message, dialog: IntentDialog(stringLiteral: message))
    }
}

/// Opens a URL and asks Device Agent to summarize the page.
struct SummarizeURLWithDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Summarize URL with Device Agent"
    static var description = IntentDescription(
        "Opens a web page in Device Agent and summarizes the main points from the page."
    )
    static var openAppWhenRun = true

    @Parameter(title: "URL")
    var url: URL

    static var parameterSummary: some ParameterSummary {
        Summary("Summarize \(\.$url) with Device Agent")
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        let message = try DeviceAgentIntentActions.browse(
            url: url,
            prompt: "Summarize the main points from this page as short bullets."
        )
        return .result(value: message, dialog: IntentDialog(stringLiteral: message))
    }
}

/// Opens a URL and asks Device Agent to find something on the page.
struct FindOnPageWithDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Find on Page with Device Agent"
    static var description = IntentDescription(
        "Opens a web page in Device Agent and searches the page for the query you provide."
    )
    static var openAppWhenRun = true

    @Parameter(title: "URL")
    var url: URL

    @Parameter(title: "Query")
    var query: String

    static var parameterSummary: some ParameterSummary {
        Summary("Find \(\.$query) on \(\.$url) with Device Agent")
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        let trimmed = query.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            throw DeviceAgentIntentError.emptyQuery
        }
        let message = try DeviceAgentIntentActions.browse(
            url: url,
            prompt: "Find \"\(trimmed)\" on this page. Use browserFind or browserSnapshot, then answer with short bullets from the page."
        )
        return .result(value: message, dialog: IntentDialog(stringLiteral: message))
    }
}

struct DeviceAgentShortcuts: AppShortcutsProvider {
    static var shortcutTileColor: ShortcutTileColor = .blue

    @AppShortcutsBuilder
    static var appShortcuts: [AppShortcut] {
        AppShortcut(
            intent: AskDeviceAgentIntent(),
            phrases: [
                "Ask Device Agent in \(.applicationName)",
                "Ask \(.applicationName) Device Agent",
                "Open Device Agent in \(.applicationName)",
            ],
            shortTitle: "Ask Agent",
            systemImageName: "bubble.left.and.text.bubble.right"
        )
        AppShortcut(
            intent: BrowseURLWithDeviceAgentIntent(),
            phrases: [
                "Browse with Device Agent in \(.applicationName)",
                "Open URL with Device Agent in \(.applicationName)",
            ],
            shortTitle: "Browse URL",
            systemImageName: "globe"
        )
        AppShortcut(
            intent: SummarizeURLWithDeviceAgentIntent(),
            phrases: [
                "Summarize URL with Device Agent in \(.applicationName)",
                "Summarize page with \(.applicationName)",
            ],
            shortTitle: "Summarize URL",
            systemImageName: "doc.text.magnifyingglass"
        )
        AppShortcut(
            intent: FindOnPageWithDeviceAgentIntent(),
            phrases: [
                "Find on page with Device Agent in \(.applicationName)",
                "Search page with Device Agent in \(.applicationName)",
            ],
            shortTitle: "Find on Page",
            systemImageName: "magnifyingglass"
        )
    }
}

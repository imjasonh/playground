import AppIntents
import Foundation
import SwiftUI

/// Shortcut / Siri entry: queue a browser prompt, then open Device Agent.
struct AskDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Ask Device Agent"
    static var description = IntentDescription(
        "Queues a Device Agent browser prompt and opens Playground."
    )
    static var openAppWhenRun = true

    @Parameter(title: "Prompt")
    var prompt: String

    static var parameterSummary: some ParameterSummary {
        Summary("Ask Device Agent \(\.$prompt)")
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        AgentInbox.shared.enqueue(prompt: prompt, source: .shortcut)
        PlaygroundRouter.shared.openDeviceAgent()
        let message = "Queued for Device Agent."
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
            systemImageName: "globe"
        )
    }
}

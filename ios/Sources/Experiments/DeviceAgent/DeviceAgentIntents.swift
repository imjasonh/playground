import AppIntents
import Foundation
import UniformTypeIdentifiers

/// Shortcut / Siri entry: queue a prompt (and optional files), then open the app.
struct RunDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Run Device Agent"
    static var description = IntentDescription(
        "Sends a prompt to Playground’s Device Agent, optionally with files, and opens the experiment."
    )
    static var openAppWhenRun = true

    @Parameter(title: "Prompt")
    var prompt: String

    @Parameter(title: "Files")
    var files: [IntentFile]?

    @Parameter(title: "Mode")
    var mode: DeviceAgentModeAppEnum?

    @Parameter(title: "Start in voice mode")
    var preferVoice: Bool?

    static var parameterSummary: some ParameterSummary {
        Summary("Run Device Agent with \(\.$prompt)") {
            \.$files
            \.$mode
            \.$preferVoice
        }
    }

    @MainActor
    func perform() async throws -> some IntentResult & ProvidesDialog {
        var attachmentIDs: [UUID] = []
        for file in files ?? [] {
            let attachment = try importIntentFile(file)
            attachmentIDs.append(attachment.id)
        }

        let resolvedMode = mode?.agentMode ?? .act
        AgentInbox.shared.enqueue(
            prompt: prompt,
            source: .shortcut,
            mode: resolvedMode,
            preferVoice: preferVoice ?? false,
            attachmentIDs: attachmentIDs
        )
        PlaygroundRouter.shared.openDeviceAgent()

        if attachmentIDs.isEmpty {
            return .result(dialog: "Opening Device Agent with your prompt.")
        }
        return .result(
            dialog: "Opening Device Agent with your prompt and \(attachmentIDs.count) file(s)."
        )
    }

    @MainActor
    private func importIntentFile(_ file: IntentFile) throws -> AgentAttachment {
        let name = file.filename.isEmpty ? "shortcut-file" : file.filename
        let data = file.data
        let temp = FileManager.default.temporaryDirectory.appendingPathComponent(
            "\(UUID().uuidString)-\(name)"
        )
        try data.write(to: temp, options: .atomic)
        defer { try? FileManager.default.removeItem(at: temp) }
        return try AgentInbox.shared.importFile(
            from: temp,
            preferredName: name,
            utType: nil
        )
    }
}

enum DeviceAgentModeAppEnum: String, AppEnum {
    case observe
    case act
    case browse

    static var typeDisplayRepresentation = TypeDisplayRepresentation(name: "Device Agent Mode")
    static var caseDisplayRepresentations: [DeviceAgentModeAppEnum: DisplayRepresentation] = [
        .observe: "Observe",
        .act: "Act",
        .browse: "Browse",
    ]

    var agentMode: AgentMode {
        switch self {
        case .observe: return .observe
        case .act: return .act
        case .browse: return .browse
        }
    }
}

struct AskDeviceAgentIntent: AppIntent {
    static var title: LocalizedStringResource = "Ask Device Agent"
    static var description = IntentDescription(
        "Queues a Device Agent prompt and opens Playground for the run and any confirmations."
    )
    static var openAppWhenRun = true

    @Parameter(title: "Prompt")
    var prompt: String

    static var parameterSummary: some ParameterSummary {
        Summary("Ask Device Agent \(\.$prompt)")
    }

    @MainActor
    func perform() async throws -> some IntentResult & ReturnsValue<String> & ProvidesDialog {
        AgentInbox.shared.enqueue(prompt: prompt, source: .shortcut, mode: .act)
        PlaygroundRouter.shared.openDeviceAgent()
        let message = "Queued for Device Agent. Confirm any writes in the Playground app."
        return .result(value: message, dialog: IntentDialog(stringLiteral: message))
    }
}

struct DeviceAgentShortcuts: AppShortcutsProvider {
    static var appShortcuts: [AppShortcut] {
        [
            AppShortcut(
                intent: RunDeviceAgentIntent(),
                phrases: [
                    "Run Device Agent in \(.applicationName)",
                    "Ask \(.applicationName) Device Agent",
                ],
                shortTitle: "Device Agent",
                systemImageName: "cpu"
            ),
            AppShortcut(
                intent: AskDeviceAgentIntent(),
                phrases: [
                    "Ask Device Agent in \(.applicationName)",
                ],
                shortTitle: "Ask Agent",
                systemImageName: "text.bubble"
            ),
        ]
    }
}

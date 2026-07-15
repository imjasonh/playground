import Foundation
import SwiftUI
#if canImport(FoundationModels)
import FoundationModels
#endif

struct ChatMessage: Identifiable, Equatable {
    enum Role: Equatable {
        case user
        case assistant
        case tool
        case system
    }

    let id: UUID
    let role: Role
    let text: String

    init(id: UUID = UUID(), role: Role, text: String) {
        self.id = id
        self.role = role
        self.text = text
    }
}

enum ModelAvailabilityState: Equatable {
    case checking
    case available
    case unavailable(String)
}

@MainActor
final class TriageChatModel: ObservableObject {
    @Published var availability: ModelAvailabilityState = .checking
    @Published var messages: [ChatMessage] = []
    @Published var draft: String = ""
    @Published var isResponding = false

    #if canImport(FoundationModels)
    /// Boxed so the property type isn't `LanguageModelSession` at the class
    /// level (that type is macOS 26-only; this class targets older macOS too).
    private var sessionBox: Any?
    /// Same boxing for `ToolActivityHub` (macOS 26-only).
    private var toolHubBox: Any?
    #endif

    static let scenarioPrompts: [(title: String, prompt: String)] = [
        (
            "Can't load websites",
            "I can't load websites in my browser. Wi‑Fi shows connected. Please diagnose routing, DNS, proxy, and connectivity, then propose fixes I can apply myself."
        ),
        (
            "VPN but broken",
            "My VPN is connected but nothing works (or only some sites work). Check whether the default route and DNS are stuck on the VPN and propose fixes."
        ),
        (
            "DNS feels wrong",
            "DNS seems broken — names won't resolve or resolve oddly. Inspect DNS config, try a lookup, and propose fixes. Don't change anything yourself."
        ),
        (
            "Only some sites fail",
            "Some websites work but others fail. Help me separate DNS vs routing vs proxy/VPN vs hosts-file issues and propose what I should try."
        ),
        (
            "Captive portal / hotel Wi‑Fi",
            "I might be behind a captive portal (hotel/cafe Wi‑Fi). Probe connectivity and propose how I should complete login — don't change settings for me."
        ),
        (
            "App using too much memory",
            "An app feels slow — please measure its live memory and CPU on this Mac (include helper processes), tell me if usage looks high, and propose what I should try. Don’t kill anything."
        ),
        (
            "Mac feels slow",
            "This Mac feels slow overall. Check disk free space, memory pressure, load average, and top CPU processes, then propose what I should try."
        ),
        (
            "Port already in use",
            "Something won’t start because a TCP port is already in use (e.g. 3000). Show which process is listening and propose what I should do — don’t kill anything."
        ),
    ]

    init() {
        refreshAvailability()
        resetSession()
    }

    func refreshAvailability() {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *) {
            let model = SystemLanguageModel.default
            if model.isAvailable {
                availability = .available
            } else {
                availability = .unavailable(unavailableReason(for: model))
            }
            return
        }
        #endif
        availability = .unavailable(
            "On-device Apple Intelligence (Foundation Models) needs macOS 26+ with Apple Intelligence enabled. Open Settings to enable it if supported, or use the Toolbox tab."
        )
    }

    func resetSession() {
        messages.removeAll()
        recreateLanguageSession()
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), sessionBox != nil {
            messages.append(
                ChatMessage(
                    role: .system,
                    text: "Ask what’s going wrong — I can measure network/config and app CPU/memory on this Mac. I propose steps; I won’t change settings or kill processes."
                )
            )
        }
        #endif
    }

    /// Builds a fresh tool-using `LanguageModelSession` without clearing chat history.
    private func recreateLanguageSession(focus: TriageHeuristics.Focus? = nil) {
        #if canImport(FoundationModels)
        sessionBox = nil
        toolHubBox = nil
        if #available(macOS 26.0, *), case .available = availability {
            let hub = ToolActivityHub { [weak self] name in
                Task { @MainActor in
                    self?.messages.append(
                        ChatMessage(role: .tool, text: "Ran \(name)…")
                    )
                }
            }
            toolHubBox = hub
            sessionBox = LanguageModelSession(
                tools: DiagnosticToolset.make(activity: hub, focus: focus),
                instructions: TriageInstructions.text
            )
        }
        #endif
    }

    func useScenario(_ prompt: String) {
        draft = prompt
    }

    func send() async {
        let text = draft.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !text.isEmpty, !isResponding else { return }
        draft = ""
        messages.append(ChatMessage(role: .user, text: text))

        #if canImport(FoundationModels)
        if #available(macOS 26.0, *) {
            refreshAvailability()
            guard case .available = availability else {
                messages.append(
                    ChatMessage(
                        role: .system,
                        text: "Apple Intelligence isn’t available right now. Use the Toolbox tab, or enable Apple Intelligence and start a new chat."
                    )
                )
                return
            }

            isResponding = true
            defer { isResponding = false }

            // Skip the no-tools gate when heuristics (or scenario chips) say we
            // can measure something live — including slow apps / memory / CPU.
            if !shouldUseDiagnosticTools(text) {
                do {
                    if let direct = try await answerWithoutTools(text) {
                        messages.append(ChatMessage(role: .assistant, text: direct))
                        return
                    }
                } catch {
                    // Gate failed — fall through to diagnostics / failure mapping.
                }
            }

            // Fresh session per diagnostic turn (4k context; tools are expensive).
            let focus = TriageHeuristics.focus(for: text) ?? .general
            recreateLanguageSession(focus: focus)
            guard let session = sessionBox as? LanguageModelSession else { return }
            let hub = toolHubBox as? ToolActivityHub
            hub?.clearReports()

            do {
                let response = try await session.respond(to: diagnosticPrompt(forLatestUserText: text))
                let content = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
                messages.append(
                    ChatMessage(
                        role: .assistant,
                        text: content.isEmpty ? "(No response text.)" : content
                    )
                )
            } catch {
                let collected = hub?.fallbackMarkdown()
                recreateLanguageSession()
                if let collected, !collected.isEmpty {
                    messages.append(
                        ChatMessage(
                            role: .assistant,
                            text: """
                                Apple Intelligence stalled after gathering diagnostics. Here’s what I collected — open the Toolbox tab for more, or tap New chat and try again.

                                \(collected)
                                """
                        )
                    )
                } else {
                    messages.append(
                        ChatMessage(
                            role: .system,
                            text: TriageFailureMessage.from(error)
                        )
                    )
                }
            }
            return
        }
        #endif

        messages.append(
            ChatMessage(
                role: .system,
                text: "Chat requires Foundation Models on macOS 26+ with Apple Intelligence. Use the Toolbox tab on this Mac."
            )
        )
    }

    private func shouldUseDiagnosticTools(_ text: String) -> Bool {
        isKnownScenario(text) || TriageHeuristics.needsLiveDiagnostics(text)
    }

    private func isKnownScenario(_ text: String) -> Bool {
        Self.scenarioPrompts.contains { $0.prompt == text }
    }

    /// Fresh FM sessions don't keep chat history — pack recent turns so follow-ups
    /// like “is it using too much memory?” still resolve to the named app.
    private func diagnosticPrompt(forLatestUserText latest: String) -> String {
        let recent = messages.suffix(12).compactMap { message -> String? in
            switch message.role {
            case .user: return "User: \(message.text)"
            case .assistant: return "Geek Squad: \(message.text)"
            case .tool, .system: return nil
            }
        }
        var lines: [String] = [
            "Recent chat (for context; answer the latest user message):",
        ]
        lines.append(contentsOf: recent)
        lines.append("")
        lines.append(
            "Use tools for live facts. If the user says “it” or omits the app name, reuse the app from earlier turns (e.g. process_usage query: Cursor)."
        )
        lines.append("Latest user message: \(latest)")
        return lines.joined(separator: "\n")
    }

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    private func answerWithoutTools(_ text: String) async throws -> String? {
        let gate = LanguageModelSession(instructions: TriageGate.instructions)
        let response = try await gate.respond(to: text)
        return TriageGate.directAnswer(from: response.content)
    }

    @available(macOS 26.0, *)
    private func unavailableReason(for model: SystemLanguageModel) -> String {
        // Keep this resilient across SDK refinements of Availability.Reason.
        if model.isAvailable {
            return "Model reported unavailable."
        }
        return "Apple Intelligence isn’t available (off, ineligible, or model not ready). Open Settings to enable it if supported, or use the Toolbox tab."
    }
    #endif
}

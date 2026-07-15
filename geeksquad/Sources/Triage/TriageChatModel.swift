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
    private var session: LanguageModelSession?
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
            "On-device Apple Intelligence (Foundation Models) needs macOS 26+ with Apple Intelligence enabled. Use the Toolbox tab for manual checks."
        )
    }

    func resetSession() {
        messages.removeAll()
        #if canImport(FoundationModels)
        session = nil
        if #available(macOS 26.0, *), case .available = availability {
            let hub = ToolActivityHub { [weak self] name in
                Task { @MainActor in
                    self?.messages.append(
                        ChatMessage(role: .tool, text: "Ran \(name)…")
                    )
                }
            }
            session = LanguageModelSession(
                tools: DiagnosticToolset.make(activity: hub),
                instructions: TriageInstructions.text
            )
            messages.append(
                ChatMessage(
                    role: .system,
                    text: "Describe what you’re seeing and what you want fixed. I’ll run local diagnostics and propose steps — I won’t change settings myself."
                )
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
            if session == nil {
                resetSession()
            }
            guard let session else { return }

            isResponding = true
            defer { isResponding = false }
            do {
                let response = try await session.respond(to: text)
                let content = response.content.trimmingCharacters(in: .whitespacesAndNewlines)
                messages.append(
                    ChatMessage(
                        role: .assistant,
                        text: content.isEmpty ? "(No response text.)" : content
                    )
                )
            } catch {
                messages.append(
                    ChatMessage(
                        role: .system,
                        text: "Triage failed: \(error.localizedDescription)"
                    )
                )
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

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    private func unavailableReason(for model: SystemLanguageModel) -> String {
        // Keep this resilient across SDK refinements of Availability.Reason.
        if model.isAvailable {
            return "Model reported unavailable."
        }
        return "Apple Intelligence isn’t available (off, ineligible, or model not ready). Enable it in System Settings if supported, or use the Toolbox tab."
    }
    #endif
}

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
    /// Set for `.tool` messages so the UI can show a short label + expandable body.
    let toolName: String?
    /// Structured closing card when the diagnostic path returns a TriageReport.
    let triageReport: TriageReportViewModel?

    init(
        id: UUID = UUID(),
        role: Role,
        text: String,
        toolName: String? = nil,
        triageReport: TriageReportViewModel? = nil
    ) {
        self.id = id
        self.role = role
        self.text = text
        self.toolName = toolName
        self.triageReport = triageReport
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
    /// Assistant bubble currently streaming — tool cards insert above it.
    private var streamingAssistantId: UUID?

    #if canImport(FoundationModels)
    /// Boxed so the property type isn't `LanguageModelSession` at the class
    /// level (that type is macOS 26-only; this class targets older macOS too).
    private var sessionBox: Any?
    /// Same boxing for `ToolActivityHub` (macOS 26-only).
    private var toolHubBox: Any?
    #endif

    nonisolated static let scenarioPrompts: [(title: String, prompt: String)] = [
        (
            "Can't get online",
            "I can't get online — browsers won't load sites even though Wi‑Fi looks connected. Run a full offline connectivity investigation (path, route, DNS, proxy, VPN, hosts, probes) and propose fixes."
        ),
        (
            "VPN but broken",
            "My VPN is connected but nothing works (or only some sites work). Check whether the default route and DNS are stuck on the VPN and propose fixes."
        ),
        (
            "DNS feels wrong",
            "DNS seems broken — names won't resolve or resolve oddly. Inspect DNS config, try a lookup, and propose fixes."
        ),
        (
            "Only some sites fail",
            "Some websites work but others fail. Help me separate DNS vs routing vs proxy/VPN vs hosts-file issues and propose what I should try."
        ),
        (
            "Captive portal / hotel Wi‑Fi",
            "I might be behind a captive portal (hotel/cafe Wi‑Fi). Probe connectivity and propose how I should complete login."
        ),
    ]

    init() {
        refreshAvailability()
        resetSession()
    }

    func refreshAvailability() {
        let status = FoundationModelsGateModel.evaluate()
        switch status {
        case .checking:
            availability = .checking
        case .available:
            availability = .available
        case .needsAppleIntelligenceEnabled:
            availability = .unavailable(
                "Apple Intelligence is off. Enable it in System Settings and wait for the on-device model to download — Onramp Chat needs it."
            )
        case .modelNotReady:
            availability = .unavailable(
                "The on-device Foundation Model is still downloading. Keep the Mac awake and plugged in, then tap New chat when it’s ready."
            )
        case .unsupportedOperatingSystem:
            availability = .unavailable(
                "Onramp requires macOS 26+ with Apple Intelligence. This OS can’t run the on-device Foundation Model."
            )
        case .deviceNotEligible:
            availability = .unavailable(
                "This Mac isn’t eligible for Apple Intelligence, so Onramp Chat can’t run here."
            )
        case .unavailableOther(let detail):
            availability = .unavailable(detail)
        }
    }

    func resetSession() {
        messages.removeAll()
        recreateLanguageSession()
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), sessionBox != nil {
            messages.append(
                ChatMessage(
                    role: .system,
                    text: "Ask what’s going wrong online — I’ll run the read-only network checks myself, then suggest practical System Settings steps."
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
            let hub = ToolActivityHub { [weak self] name, markdown in
                Task { @MainActor in
                    self?.insertToolMessage(name: name, markdown: markdown)
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

    /// Starter / follow-up chips: fill the composer and send immediately.
    func sendScenario(_ prompt: String) async {
        useScenario(prompt)
        await send()
    }

    /// Markdown transcript for sharing / pasting into a ticket.
    func copyTranscript() {
        let body = messages.map { message -> String in
            switch message.role {
            case .user: return "**You:** \(message.text)"
            case .assistant:
                if let report = message.triageReport {
                    return "**Onramp:**\n\(report.markdown)"
                }
                return "**Onramp:** \(message.text)"
            case .tool:
                let label = message.toolName.map { "Tool (\($0))" } ?? "Tool"
                return "**\(label):**\n```\n\(message.text)\n```"
            case .system: return "**Note:** \(message.text)"
            }
        }.joined(separator: "\n\n")
        PasteboardCopy.string(body)
    }

    var followUpPrompts: [(title: String, prompt: String)] {
        guard !isResponding,
              messages.contains(where: { $0.role == .assistant || $0.role == .tool })
        else { return [] }
        return [
            ("Recheck", "Please re-run the most relevant live checks for my last question and tell me what changed."),
            ("Disk + folders", "Check disk free space and user storage hotspots (Downloads/Caches), then propose what to clean."),
            ("Login agents", "List launch agents / login-related plists and say if the count looks high for a slow Mac."),
            ("Battery", "Check whether this Mac is on battery or AC and if that could explain slowness."),
        ]
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
            // can measure something live — including Recheck / “what changed”.
            if !shouldUseDiagnosticTools(text) {
                do {
                    let answered = try await streamPlainAnswer(
                        to: text,
                        instructions: TriageGate.instructions
                    )
                    if answered { return }
                    // Model replied DIAGNOSE (or empty) — fall through to tools.
                } catch {
                    // Gate/stream failed — fall through to diagnostics / failure mapping.
                }
            }

            // Fresh session per diagnostic turn (4k context; tools are expensive).
            let focus = focusForTurn(text)
            recreateLanguageSession(focus: focus)
            guard let session = sessionBox as? LanguageModelSession else { return }
            let hub = toolHubBox as? ToolActivityHub
            hub?.clearReports()

            do {
                try await streamTriageReport(
                    session: session,
                    prompt: diagnosticPrompt(forLatestUserText: text)
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

    /// Prefer keywords on this turn; for Recheck, reuse focus from an earlier user turn.
    private func focusForTurn(_ text: String) -> TriageHeuristics.Focus {
        if let focus = TriageHeuristics.focus(for: text) {
            return focus
        }
        if TriageHeuristics.isRecheckFollowUp(text) {
            for message in messages.reversed() {
                guard message.role == .user, message.text != text else { continue }
                if let focus = TriageHeuristics.focus(for: message.text) {
                    return focus
                }
            }
        }
        return .general
    }

    /// Fresh FM sessions don't keep chat history — pack recent turns so follow-ups
    /// like “is it using too much memory?” still resolve to the named app.
    private func diagnosticPrompt(forLatestUserText latest: String) -> String {
        let recheck = TriageHeuristics.isRecheckFollowUp(latest)
        let recent = messages.suffix(12).compactMap { message -> String? in
            switch message.role {
            case .user: return "User: \(message.text)"
            case .assistant:
                if let report = message.triageReport {
                    // Full prior report so “what changed” can compare evidence.
                    return "Onramp previous report:\n\(report.markdown)"
                }
                let clipped = message.text.count > 600
                    ? String(message.text.prefix(600)) + "…"
                    : message.text
                return "Onramp: \(clipped)"
            case .tool:
                guard recheck else { return nil }
                let label = message.toolName.map { "Prior tool (\($0))" } ?? "Prior tool"
                let clipped = message.text.count > 500
                    ? String(message.text.prefix(500)) + "…"
                    : message.text
                return "\(label):\n\(clipped)"
            case .system: return nil
            }
        }
        var lines: [String] = [
            "Recent chat (for context; answer the latest user message):",
        ]
        lines.append(contentsOf: recent)
        lines.append("")
        lines.append(
            "You have this chat history — never claim you cannot see past questions."
        )
        lines.append(
            "Use tools for live facts — do not ask the user to run Terminal diagnostics. If the user says “it” or omits the app name, reuse the app from earlier turns (e.g. process_usage query: Cursor)."
        )
        if recheck {
            lines.append(
                "This is a recheck: call the same kinds of tools again and say what changed versus the previous report/evidence above."
            )
        }
        lines.append(
            "Fill the triage report from tool evidence only. proposedSteps must be Settings/UI remediations the user can do — never Terminal read-only commands Onramp could have run as tools."
        )
        lines.append("Latest user message: \(latest)")
        return lines.joined(separator: "\n")
    }

    /// Pack recent turns for the no-tools path so follow-ups aren't answered blind.
    private func plainPrompt(forLatestUserText latest: String) -> String {
        let prior = messages.dropLast().suffix(8).compactMap { message -> String? in
            switch message.role {
            case .user: return "User: \(message.text)"
            case .assistant:
                if let report = message.triageReport {
                    return "Onramp: \(report.headline) — \(report.likelyCause)"
                }
                let clipped = message.text.count > 400
                    ? String(message.text.prefix(400)) + "…"
                    : message.text
                return "Onramp: \(clipped)"
            case .tool, .system: return nil
            }
        }
        guard !prior.isEmpty else { return latest }
        return """
            Recent chat (for context; answer the latest user message):
            \(prior.joined(separator: "\n"))

            You have this chat history — never claim you cannot see past questions in this conversation. If the user needs fresh live measurements, reply \(TriageGate.diagnoseSentinel).

            Latest user message: \(latest)
            """
    }

    private func replaceMessage(id: UUID, with message: ChatMessage) {
        guard let index = messages.firstIndex(where: { $0.id == id }) else {
            messages.append(message)
            return
        }
        messages[index] = message
    }

    /// Keep tool cards above the in-progress assistant reply.
    private func insertToolMessage(name: String, markdown: String) {
        let tool = ChatMessage(role: .tool, text: markdown, toolName: name)
        if let aid = streamingAssistantId,
           let idx = messages.firstIndex(where: { $0.id == aid })
        {
            messages.insert(tool, at: idx)
        } else {
            messages.append(tool)
        }
    }

    #if canImport(FoundationModels)
    /// Streams a no-tools reply. Returns `false` when the model asked for diagnostics
    /// (`DIAGNOSE`) so the caller can fall through to the tool path.
    @available(macOS 26.0, *)
    @discardableResult
    private func streamPlainAnswer(to text: String, instructions: String) async throws -> Bool {
        let session = LanguageModelSession(instructions: instructions)
        let id = UUID()
        streamingAssistantId = id
        defer { streamingAssistantId = nil }
        messages.append(ChatMessage(id: id, role: .assistant, text: ""))
        let stream = session.streamResponse(to: plainPrompt(forLatestUserText: text))
        for try await snapshot in stream {
            let textOut = snapshot.content.trimmingCharacters(in: .whitespacesAndNewlines)
            replaceMessage(
                id: id,
                with: ChatMessage(id: id, role: .assistant, text: textOut.isEmpty ? "…" : textOut)
            )
        }
        if let last = messages.first(where: { $0.id == id }) {
            if TriageGate.needsDiagnostics(last.text) {
                messages.removeAll { $0.id == id }
                return false
            }
            if last.text.isEmpty || last.text == "…" {
                replaceMessage(
                    id: id,
                    with: ChatMessage(id: id, role: .assistant, text: "(No response text.)")
                )
            }
        }
        return true
    }

    @available(macOS 26.0, *)
    private func streamTriageReport(session: LanguageModelSession, prompt: String) async throws {
        let id = UUID()
        streamingAssistantId = id
        defer { streamingAssistantId = nil }
        messages.append(ChatMessage(id: id, role: .assistant, text: "Working…"))
        let stream = session.streamResponse(to: prompt, generating: TriageReport.self)
        for try await snapshot in stream {
            let partial = snapshot.content
            let report = TriageReportViewModel(
                headline: partial.headline ?? "Working…",
                likelyCause: partial.likelyCause ?? "",
                evidence: partial.evidence ?? [],
                proposedSteps: partial.proposedSteps ?? []
            )
            replaceMessage(
                id: id,
                with: ChatMessage(
                    id: id,
                    role: .assistant,
                    text: report.markdown,
                    triageReport: report
                )
            )
        }
        if let last = messages.first(where: { $0.id == id }),
           last.triageReport == nil || (last.triageReport?.headline.isEmpty ?? true)
        {
            replaceMessage(
                id: id,
                with: ChatMessage(id: id, role: .assistant, text: "(No triage report.)")
            )
        }
    }

    #endif
}

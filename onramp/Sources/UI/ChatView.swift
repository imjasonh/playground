import AppKit
import SwiftUI

struct ChatView: View {
    @EnvironmentObject private var foundationModelsGate: FoundationModelsGateModel
    @StateObject private var model = TriageChatModel()
    @FocusState private var composerFocused: Bool

    var body: some View {
        Group {
            if foundationModelsGate.status == .available {
                chatBody
            } else {
                chatUnavailableBody
            }
        }
        .navigationTitle("Onramp")
        .onAppear {
            model.refreshAvailability()
        }
        .onChange(of: foundationModelsGate.status) { _, newStatus in
            model.refreshAvailability()
            if newStatus == .available {
                model.resetSession()
            }
        }
    }

    private var chatBody: some View {
        VStack(spacing: 0) {
            messageList
            if model.messages.count <= 1 {
                scenarioChips
            } else if !model.followUpPrompts.isEmpty {
                followUpChips
            }
            composer
        }
        .toolbar {
            ToolbarItem(placement: .automatic) {
                Button("Copy chat") {
                    model.copyTranscript()
                }
                .disabled(model.messages.isEmpty)
                .accessibilityIdentifier("copy-chat")
            }
            ToolbarItem(placement: .primaryAction) {
                Button("New chat") {
                    foundationModelsGate.refresh()
                    model.refreshAvailability()
                    model.resetSession()
                }
                .disabled(model.isResponding)
                .accessibilityIdentifier("new-chat")
            }
        }
    }

    /// Shown when the user bypassed the gate with Playbooks-only — Chat still demands setup.
    private var chatUnavailableBody: some View {
        VStack(spacing: 20) {
            Spacer(minLength: 12)
            Image(systemName: foundationModelsGate.status == .modelNotReady
                  ? "arrow.down.circle.fill"
                  : "apple.logo")
                .font(.system(size: 48))
                .foregroundStyle(.tint)
            Text("Chat needs the on-device model")
                .font(.title2.weight(.bold))
            Text(chatUnavailableCopy)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: 420)
            if foundationModelsGate.status.isSetupRequired {
                ProgressView()
                    .padding(.top, 4)
            }
            Button {
                foundationModelsGate.allowPlaybooksWithoutModel = false
                foundationModelsGate.refresh()
            } label: {
                Text("Finish Apple Intelligence setup…")
                    .frame(maxWidth: 320)
            }
            .buttonStyle(.borderedProminent)
            .controlSize(.large)
            .accessibilityIdentifier("chat-finish-setup")
            Button("Open Settings") {
                foundationModelsGate.openSettingsAndRefresh()
            }
            .buttonStyle(.bordered)
            Spacer(minLength: 12)
        }
        .padding(32)
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityIdentifier("chat-model-required")
    }

    private var chatUnavailableCopy: String {
        switch foundationModelsGate.status {
        case .modelNotReady:
            return "The Foundation Model is still downloading. Playbooks work without it; Chat does not."
        case .needsAppleIntelligenceEnabled:
            return "Enable Apple Intelligence and wait for the model download. Playbooks work without Chat; Chat does not."
        case .unsupportedOperatingSystem, .deviceNotEligible:
            return "This Mac can’t run Apple Intelligence, so Chat is unavailable."
        default:
            return "Finish on-device model setup to use Chat. Playbooks remain available for can’t-get-online triage."
        }
    }

    private var messageList: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 12) {
                    ForEach(model.messages) { message in
                        MessageBubble(message: message)
                            .id(message.id)
                    }
                    if model.isResponding,
                       model.messages.last?.role != .assistant
                        || (model.messages.last?.text.isEmpty ?? true)
                    {
                        Text("Working…")
                            .font(.callout)
                            .foregroundStyle(.secondary)
                            .padding(.horizontal, 4)
                            .id("working")
                    }
                }
                .padding(16)
            }
            .onChange(of: model.messages.count) { _, _ in
                scrollToLatest(proxy)
            }
            .onChange(of: model.messages.last?.text) { _, _ in
                scrollToLatest(proxy)
            }
            .onChange(of: model.isResponding) { _, responding in
                if responding { scrollToLatest(proxy) }
            }
        }
    }

    private func scrollToLatest(_ proxy: ScrollViewProxy) {
        if let last = model.messages.last?.id {
            withAnimation {
                proxy.scrollTo(last, anchor: .bottom)
            }
        } else if model.isResponding {
            withAnimation {
                proxy.scrollTo("working", anchor: .bottom)
            }
        }
    }

    private var scenarioChips: some View {
        chipRow(TriageChatModel.scenarioPrompts)
    }

    private var followUpChips: some View {
        chipRow(model.followUpPrompts)
    }

    private func chipRow(_ items: [(title: String, prompt: String)]) -> some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 8) {
                ForEach(items, id: \.title) { item in
                    Button(item.title) {
                        Task { await model.sendScenario(item.prompt) }
                    }
                    .buttonStyle(.bordered)
                    .disabled(model.isResponding)
                    .accessibilityIdentifier("chip-\(item.title)")
                }
            }
            .padding(.horizontal, 16)
            .padding(.vertical, 8)
        }
    }

    private var composer: some View {
        HStack(alignment: .bottom, spacing: 10) {
            TextField(
                "What are you seeing, and what do you want fixed?",
                text: $model.draft,
                axis: .vertical
            )
            .lineLimit(1...6)
            .textFieldStyle(.plain)
            .padding(10)
            .background(Color.primary.opacity(0.06))
            .clipShape(RoundedRectangle(cornerRadius: 8))
            .focused($composerFocused)
            .disabled(model.isResponding)
            .accessibilityIdentifier("chat-composer")
            .onSubmit {
                Task { await model.send() }
            }

            Button {
                Task { await model.send() }
            } label: {
                Image(systemName: "arrow.up.circle.fill")
                    .font(.title)
            }
            .buttonStyle(.plain)
            .disabled(
                model.isResponding
                    || model.draft.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
            )
            .accessibilityIdentifier("chat-send")
            .keyboardShortcut(.return, modifiers: [.command])
        }
        .padding(12)
        .background(.bar)
    }
}

private struct MessageBubble: View {
    let message: ChatMessage
    @State private var toolExpanded = false

    var body: some View {
        HStack(alignment: .top) {
            if message.role == .user { Spacer(minLength: 40) }
            VStack(alignment: message.role == .user ? .trailing : .leading, spacing: 6) {
                HStack(spacing: 8) {
                    Text(roleLabel)
                        .font(.caption2.weight(.semibold))
                        .foregroundStyle(.secondary)
                    if message.role != .user {
                        Button {
                            PasteboardCopy.string(message.triageReport?.markdown ?? message.text)
                        } label: {
                            Image(systemName: "doc.on.doc")
                                .font(.caption)
                        }
                        .buttonStyle(.plain)
                        .help("Copy")
                        .accessibilityIdentifier("copy-message")
                    }
                }

                if let report = message.triageReport {
                    TriageReportCard(report: report)
                } else if message.role == .tool {
                    DisclosureGroup(isExpanded: $toolExpanded) {
                        Text(message.text)
                            .textSelection(.enabled)
                            .font(.caption.monospaced())
                            .frame(maxWidth: .infinity, alignment: .leading)
                            .fixedSize(horizontal: false, vertical: true)
                    } label: {
                        Text(toolLabel)
                            .font(.callout.weight(.medium))
                    }
                } else if message.role == .assistant || message.role == .system {
                    MarkdownText(source: message.text)
                } else {
                    Text(message.text)
                        .textSelection(.enabled)
                        .font(.body)
                        .fixedSize(horizontal: false, vertical: true)
                }
            }
            .padding(10)
            .frame(maxWidth: 560, alignment: message.role == .user ? .trailing : .leading)
            .background(background)
            .clipShape(RoundedRectangle(cornerRadius: 10))
            if message.role != .user { Spacer(minLength: 40) }
        }
    }

    private var toolLabel: String {
        if let name = message.toolName {
            return toolExpanded ? "Hide \(name) results" : "Ran \(name) — show results"
        }
        return toolExpanded ? "Hide tool results" : "Show tool results"
    }

    private var roleLabel: String {
        switch message.role {
        case .user: return "You"
        case .assistant: return "Onramp"
        case .tool: return "Tool"
        case .system: return "Note"
        }
    }

    private var background: Color {
        switch message.role {
        case .user: return Color.accentColor.opacity(0.15)
        case .assistant: return Color.primary.opacity(0.06)
        case .tool: return Color.cyan.opacity(0.10)
        case .system: return Color.orange.opacity(0.10)
        }
    }
}

#Preview {
    NavigationStack {
        ChatView()
            .environmentObject(FoundationModelsGateModel())
    }
    .frame(width: 640, height: 480)
}

import AppKit
import SwiftUI

struct ChatView: View {
    @StateObject private var model = TriageChatModel()
    @FocusState private var composerFocused: Bool

    var body: some View {
        VStack(spacing: 0) {
            availabilityBanner
            messageList
            if case .available = model.availability, model.messages.count <= 1 {
                scenarioChips
            } else if !model.followUpPrompts.isEmpty {
                followUpChips
            }
            composer
        }
        .navigationTitle("Geek Squad")
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
                    model.refreshAvailability()
                    model.resetSession()
                }
                .disabled(model.isResponding)
                .accessibilityIdentifier("new-chat")
            }
        }
    }

    @ViewBuilder
    private var availabilityBanner: some View {
        switch model.availability {
        case .checking:
            banner(text: "Checking Apple Intelligence…", color: .secondary, showSettingsLink: false)
        case .available:
            EmptyView()
        case .unavailable(let reason):
            banner(text: reason, color: .orange, showSettingsLink: true)
        }
    }

    private func banner(text: String, color: Color, showSettingsLink: Bool) -> some View {
        HStack(alignment: .top, spacing: 12) {
            MarkdownText(source: text, font: .callout)
                .foregroundStyle(color)
            if showSettingsLink {
                Button("Open Settings…") {
                    AppleIntelligenceSettings.open()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
                .accessibilityIdentifier("open-apple-intelligence-settings")
            }
        }
        .padding(.horizontal, 16)
        .padding(.vertical, 10)
        .background(color.opacity(0.08))
        .accessibilityIdentifier("availability-banner")
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
                        model.useScenario(item.prompt)
                        composerFocused = true
                    }
                    .buttonStyle(.bordered)
                    .disabled(model.isResponding)
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
        case .assistant: return "Geek Squad"
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
    ChatView()
        .frame(width: 640, height: 480)
}

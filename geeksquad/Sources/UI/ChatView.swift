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
            }
            composer
        }
        .navigationTitle("Geek Squad")
        .toolbar {
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
            banner(text: "Checking Apple Intelligence…", color: .secondary)
        case .available:
            EmptyView()
        case .unavailable(let reason):
            banner(text: reason, color: .orange)
        }
    }

    private func banner(text: String, color: Color) -> some View {
        Text(text)
            .font(.callout)
            .foregroundStyle(color)
            .frame(maxWidth: .infinity, alignment: .leading)
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
                    if model.isResponding {
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
                if let last = model.messages.last?.id {
                    withAnimation {
                        proxy.scrollTo(last, anchor: .bottom)
                    }
                }
            }
            .onChange(of: model.isResponding) { _, responding in
                if responding {
                    withAnimation {
                        proxy.scrollTo("working", anchor: .bottom)
                    }
                }
            }
        }
    }

    private var scenarioChips: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 8) {
                ForEach(TriageChatModel.scenarioPrompts, id: \.title) { item in
                    Button(item.title) {
                        model.useScenario(item.prompt)
                        composerFocused = true
                    }
                    .buttonStyle(.bordered)
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

    var body: some View {
        HStack {
            if message.role == .user { Spacer(minLength: 40) }
            VStack(alignment: message.role == .user ? .trailing : .leading, spacing: 4) {
                Text(roleLabel)
                    .font(.caption2.weight(.semibold))
                    .foregroundStyle(.secondary)
                Text(message.text)
                    .textSelection(.enabled)
                    .font(message.role == .tool ? .caption.monospaced() : .body)
            }
            .padding(10)
            .background(background)
            .clipShape(RoundedRectangle(cornerRadius: 10))
            if message.role != .user { Spacer(minLength: 40) }
        }
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

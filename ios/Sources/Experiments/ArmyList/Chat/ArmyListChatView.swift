import SwiftUI
import UIKit

/// On-device chat over the current army list (Foundation Models + validator tools).
struct ArmyListChatView: View {
    @Binding var list: ArmyListDocument
    let catalog: ArmyCatalog
    let store: ArmyListStore

    @StateObject private var runtime: ArmyListChatRuntime
    @State private var draft = ""
    @FocusState private var promptFocused: Bool

    init(list: Binding<ArmyListDocument>, catalog: ArmyCatalog, store: ArmyListStore) {
        self._list = list
        self.catalog = catalog
        self.store = store
        let workspace = ArmyListChatWorkspace(list: list.wrappedValue, catalog: catalog)
        _runtime = StateObject(wrappedValue: ArmyListChatRuntime(workspace: workspace))
    }

    private var prompts: [(title: String, text: String)] {
        [
            ("Build 1k", "Call seedLegalList with battleSizeID incursion and a short name for a legal 1000 point list. Then getListSummary and confirm Status."),
            ("Weaknesses", "What matchups or unit types will give this list trouble? Opinion only. Use getListSummary for the facts."),
            ("Fix errors", "Read getListSummary and fix every validation ERROR with tools. Prefer small edits. Stop when Status is LEGAL or explain what you cannot fix."),
            ("Theme", "Suggest a good army name and a paint color scheme for this list. If the user likes a name, call setListName."),
        ]
    }

    var body: some View {
        VStack(spacing: 0) {
            if runtime.isModelAvailable {
                statusBar
                transcript
                promptChips
                composer
            } else {
                unavailablePane
            }
        }
        .navigationTitle("List chat")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .primaryAction) {
                Button("Clear") { runtime.clearTranscript() }
                    .disabled(runtime.transcript.isEmpty)
                    .accessibilityIdentifier("armyListChatClear")
            }
        }
        .onAppear {
            runtime.workspace.list = list
            runtime.refreshModelStatus()
        }
        .onReceive(runtime.workspace.$list) { newList in
            list = newList
            try? store.save(newList)
        }
    }

    private var statusBar: some View {
        let result = runtime.workspace.validation
        return HStack {
            Text(result.isLegal ? "Legal" : "Illegal")
                .font(.subheadline.weight(.semibold))
                .foregroundStyle(result.isLegal ? Color.green : Color.red)
            Spacer()
            Text("\(result.totalPoints) pts · \(result.errors.count) err")
                .font(.caption)
                .foregroundStyle(.secondary)
        }
        .padding(.horizontal)
        .padding(.vertical, 8)
        .background(Color(uiColor: .secondarySystemBackground))
        .accessibilityIdentifier("armyListChatStatus")
    }

    private var transcript: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 10) {
                    ForEach(runtime.transcript) { entry in
                        chatBubble(entry)
                            .id(entry.id)
                    }
                }
                .padding()
            }
            .onChange(of: runtime.transcript.count) { _ in
                if let last = runtime.transcript.last {
                    withAnimation {
                        proxy.scrollTo(last.id, anchor: .bottom)
                    }
                }
            }
        }
    }

    private func chatBubble(_ entry: ArmyListChatEntry) -> some View {
        let alignment: HorizontalAlignment = entry.kind == .user ? .trailing : .leading
        return VStack(alignment: alignment, spacing: 2) {
            Text(label(for: entry.kind))
                .font(.caption2)
                .foregroundStyle(.secondary)
            Text(entry.text)
                .font(entry.kind == .tool ? .caption.monospaced() : .body)
                .padding(10)
                .background(bubbleColor(for: entry.kind))
                .clipShape(RoundedRectangle(cornerRadius: 12, style: .continuous))
                .frame(maxWidth: .infinity, alignment: entry.kind == .user ? .trailing : .leading)
        }
    }

    private func label(for kind: ArmyListChatEntry.Kind) -> String {
        switch kind {
        case .user: return "You"
        case .assistant: return "Assistant"
        case .system: return "System"
        case .tool: return "Tool"
        }
    }

    private func bubbleColor(for kind: ArmyListChatEntry.Kind) -> Color {
        switch kind {
        case .user:
            return Color.accentColor.opacity(0.18)
        case .assistant:
            return Color(uiColor: .secondarySystemBackground)
        case .system:
            return Color.orange.opacity(0.12)
        case .tool:
            return Color.purple.opacity(0.10)
        }
    }

    private var promptChips: some View {
        ScrollView(.horizontal, showsIndicators: false) {
            HStack(spacing: 8) {
                ForEach(Array(prompts.enumerated()), id: \.offset) { _, item in
                    Button(item.title) {
                        Task { await runtime.send(prompt: item.text) }
                    }
                    .buttonStyle(.bordered)
                    .disabled(runtime.isRunning)
                    .accessibilityIdentifier("armyListChatChip-\(item.title)")
                }
            }
            .padding(.horizontal)
            .padding(.vertical, 8)
        }
    }

    private var composer: some View {
        HStack(alignment: .bottom, spacing: 8) {
            TextField("Ask about this list…", text: $draft, axis: .vertical)
                .lineLimit(1...4)
                .focused($promptFocused)
                .accessibilityIdentifier("armyListChatDraft")
            Button {
                let text = draft
                draft = ""
                Task { await runtime.send(prompt: text) }
            } label: {
                Image(systemName: "arrow.up.circle.fill")
                    .font(.title2)
            }
            .disabled(runtime.isRunning || draft.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
            .accessibilityLabel("Send")
            .accessibilityIdentifier("armyListChatSend")
        }
        .padding()
        .background(Color(uiColor: .secondarySystemBackground))
    }

    private var unavailablePane: some View {
        VStack(spacing: 16) {
            Image(systemName: "sparkles")
                .font(.largeTitle)
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            Text(runtime.modelGate.title)
                .font(.headline)
                .multilineTextAlignment(.center)
            Text(runtime.armyListGateDetail)
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
            if let action = runtime.modelGate.primaryAction {
                Button(action.title) {
                    Task { await runtime.performModelGateAction(action) }
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("armyListChatModelGateAction")
            }
            Text("You can still build and validate lists without chat.")
                .font(.footnote)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
        }
        .padding()
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityIdentifier("armyListChatUnavailable")
    }
}

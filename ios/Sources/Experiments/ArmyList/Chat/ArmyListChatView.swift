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
    @State private var exportShare: ExportShareItem?
    @State private var exportError: String?

    private struct ExportShareItem: Identifiable {
        let id = UUID()
        let url: URL
    }

    init(list: Binding<ArmyListDocument>, catalog: ArmyCatalog, store: ArmyListStore) {
        self._list = list
        self.catalog = catalog
        self.store = store
        let workspace = ArmyListChatWorkspace(list: list.wrappedValue, catalog: catalog)
        _runtime = StateObject(wrappedValue: ArmyListChatRuntime(workspace: workspace))
    }

    private struct PromptChip: Identifiable {
        let id: String
        let title: String
        let text: String
    }

    private var prompts: [PromptChip] {
        [
            PromptChip(
                id: "fix-errors",
                title: "Fix errors",
                text: """
                Fix validation ERRORs only. Call getListSummary first. \
                Keep the current battle size — never call setBattleSize. \
                Prefer removeUnit, setUnitModels, setDetachments, setWarlord, or attachCharacter. \
                Do not add more copies of a datasheet than the battle-size duplicate limit (addUnit will reject illegal copies). \
                After each tool call, read Status; stop when LEGAL or explain what you cannot fix without changing battle size.
                """
            ),
            PromptChip(
                id: "fill-points",
                title: "Fill points",
                text: """
                Fill remaining points with a thematic extension of this list. \
                Keep battle size and existing units. Call getListSummary, note pts remaining, \
                then addUnit a few fitting datasheets (check copies N/limit in searchCatalog). \
                Never exceed the points limit or duplicate caps. Never call setBattleSize. \
                Stop when remaining points are too small for another legal unit, then briefly say what you added.
                """
            ),
            PromptChip(
                id: "weaknesses",
                title: "Weaknesses",
                text: "Weaknesses only (ignore prior theme/name talk): what matchups or unit types will give this list trouble? Opinion only. Call getListSummary for the facts."
            ),
            PromptChip(
                id: "theme",
                title: "Theme",
                text: "Theme only: suggest a good army name and a paint color scheme for this list. If the user likes a name, call setListName. Do not discuss matchup weaknesses."
            ),
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
                Menu {
                    Button {
                        exportConversation()
                    } label: {
                        Label("Export JSON", systemImage: "square.and.arrow.up")
                    }
                    .accessibilityIdentifier("armyListChatExport")
                    Button("Clear") { runtime.clearTranscript() }
                        .disabled(runtime.transcript.isEmpty)
                        .accessibilityIdentifier("armyListChatClear")
                } label: {
                    Image(systemName: "ellipsis.circle")
                }
                .accessibilityLabel("Chat options")
                .accessibilityIdentifier("armyListChatMenu")
            }
        }
        .sheet(item: $exportShare) { item in
            NavigationStack {
                VStack(alignment: .leading, spacing: 16) {
                    Text("Share this JSON dump (transcript, tool results, list, and validation) to debug List chat.")
                        .font(.footnote)
                        .foregroundStyle(.secondary)
                    ShareLink(item: item.url) {
                        Label("Share JSON", systemImage: "square.and.arrow.up")
                            .frame(maxWidth: .infinity)
                    }
                    .buttonStyle(.borderedProminent)
                    .accessibilityIdentifier("armyListChatExportShareLink")
                    Spacer()
                }
                .padding()
                .navigationTitle("Export chat")
                .navigationBarTitleDisplayMode(.inline)
                .toolbar {
                    ToolbarItem(placement: .cancellationAction) {
                        Button("Done") { exportShare = nil }
                            .accessibilityIdentifier("armyListChatExportDone")
                    }
                }
            }
            .presentationDetents([.medium])
            .accessibilityIdentifier("armyListChatExportSheet")
        }
        .alert("Export failed", isPresented: Binding(
            get: { exportError != nil },
            set: { if !$0 { exportError = nil } }
        )) {
            Button("OK", role: .cancel) { exportError = nil }
        } message: {
            Text(exportError ?? "")
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

    private func exportConversation() {
        do {
            let url = try runtime.writeConversationDumpFile()
            exportShare = ExportShareItem(url: url)
        } catch {
            exportError = error.localizedDescription
        }
    }

    private var statusBar: some View {
        let result = runtime.workspace.validation
        return HStack(spacing: 12) {
            Text(result.isLegal ? "Legal" : "Illegal")
                .font(.subheadline.weight(.semibold))
                .foregroundStyle(result.isLegal ? Color.green : Color.red)
            Spacer()
            Text("\(result.totalPoints) pts")
                .font(.caption)
                .foregroundStyle(.secondary)
            ArmyListIssueCountsLabel(
                errors: result.errors.count,
                warnings: result.warnings.count
            )
            contextRing
        }
        .padding(.horizontal)
        .padding(.vertical, 8)
        .background(Color(uiColor: .secondarySystemBackground))
        .accessibilityIdentifier("armyListChatStatus")
    }

    /// Circular fill for remaining model context (empty ring = full window free).
    private var contextRing: some View {
        let usage = runtime.contextUsage
        let remaining = max(0, 1 - usage.fractionUsed)
        let tint: Color = {
            if usage.fractionUsed >= 0.85 { return .orange }
            if usage.fractionUsed >= AgentContextBudget.compactThreshold { return .yellow }
            return .accentColor
        }()
        return ZStack {
            Circle()
                .stroke(Color.secondary.opacity(0.18), lineWidth: 3)
            Circle()
                .trim(from: 0, to: remaining)
                .stroke(tint, style: StrokeStyle(lineWidth: 3, lineCap: .round))
                .rotationEffect(.degrees(-90))
                .animation(.easeInOut(duration: 0.25), value: remaining)
            if runtime.isRunning {
                ProgressView()
                    .controlSize(.mini)
            } else {
                Text("\(Int((remaining * 100).rounded(.down)))")
                    .font(.system(size: 9, weight: .semibold, design: .rounded))
                    .monospacedDigit()
                    .foregroundStyle(.secondary)
            }
        }
        .frame(width: 28, height: 28)
        .accessibilityElement(children: .ignore)
        .accessibilityLabel(
            "\(Int((remaining * 100).rounded(.down))) percent model context remaining"
                + (usage.didCompact ? ", compacted earlier" : "")
        )
        .accessibilityIdentifier("armyListChatContextRing")
    }

    private var transcript: some View {
        let blocks = ArmyListChatTranscriptBlock.build(from: runtime.transcript)
        return ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 10) {
                    ForEach(blocks) { block in
                        transcriptBlock(block)
                            .id(block.id)
                    }
                }
                .padding()
            }
            .onChange(of: runtime.transcript.count) { _ in
                if let last = blocks.last {
                    withAnimation {
                        proxy.scrollTo(last.id, anchor: .bottom)
                    }
                }
            }
        }
    }

    @ViewBuilder
    private func transcriptBlock(_ block: ArmyListChatTranscriptBlock) -> some View {
        switch block {
        case .message(let entry):
            chatBubble(entry)
        case .tools(_, let entries):
            toolActionsGroup(entries)
        }
    }

    private func toolActionsGroup(_ entries: [ArmyListChatEntry]) -> some View {
        let labels = entries.map(\.text)
        return DisclosureGroup {
            VStack(alignment: .leading, spacing: 4) {
                ForEach(entries) { entry in
                    HStack(alignment: .firstTextBaseline, spacing: 6) {
                        Image(systemName: "wrench.and.screwdriver")
                            .font(.caption2)
                            .foregroundStyle(.purple.opacity(0.8))
                            .accessibilityHidden(true)
                        Text(entry.text)
                            .font(.caption.monospaced())
                            .foregroundStyle(.secondary)
                            .textSelection(.enabled)
                    }
                    .accessibilityIdentifier("armyListChatToolRow")
                }
            }
            .padding(.top, 4)
        } label: {
            HStack(spacing: 6) {
                Image(systemName: "ellipsis.circle")
                    .font(.caption)
                    .foregroundStyle(.purple)
                    .accessibilityHidden(true)
                Text(ArmyListChatToolDisplay.groupSummary(labels: labels))
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .lineLimit(2)
            }
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 6)
        .background(Color.purple.opacity(0.08))
        .clipShape(RoundedRectangle(cornerRadius: 10, style: .continuous))
        .accessibilityIdentifier("armyListChatToolGroup")
    }

    private func chatBubble(_ entry: ArmyListChatEntry) -> some View {
        let alignment: HorizontalAlignment = entry.kind == .user ? .trailing : .leading
        return VStack(alignment: alignment, spacing: 2) {
            Text(label(for: entry.kind))
                .font(.caption2)
                .foregroundStyle(.secondary)
            Group {
                if entry.kind == .assistant || entry.kind == .system {
                    Text(ArmyListChatMarkdown.attributed(entry.text))
                        .font(.body)
                        .textSelection(.enabled)
                } else {
                    Text(entry.text)
                        .font(.body)
                }
            }
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
                ForEach(prompts) { chip in
                    Button(chip.title) {
                        // Copy before Task — deferred capture of ForEach locals can
                        // stick on the last chip (Theme) and ignore Weaknesses/etc.
                        let title = chip.title
                        let prompt = chip.text
                        Task {
                            await runtime.send(prompt: prompt, displayText: title)
                        }
                    }
                    .buttonStyle(.bordered)
                    .disabled(runtime.isRunning)
                    .accessibilityIdentifier("armyListChatChip-\(chip.id)")
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
            Button {
                exportConversation()
            } label: {
                Label("Export JSON", systemImage: "square.and.arrow.up")
            }
            .buttonStyle(.bordered)
            .accessibilityIdentifier("armyListChatExportUnavailable")
        }
        .padding()
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityIdentifier("armyListChatUnavailable")
    }
}

/// Parses assistant Markdown into an `AttributedString` for chat bubbles.
enum ArmyListChatMarkdown {
    static func attributed(_ text: String) -> AttributedString {
        let options = AttributedString.MarkdownParsingOptions(
            interpretedSyntax: .full,
            failurePolicy: .returnPartiallyParsedIfPossible
        )
        if let parsed = try? AttributedString(
            markdown: text,
            options: options
        ) {
            return parsed
        }
        return AttributedString(text)
    }
}

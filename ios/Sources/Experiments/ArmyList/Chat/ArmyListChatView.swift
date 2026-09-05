import SwiftUI
import UIKit

/// On-device chat over the current army list (Foundation Models + validator tools).
struct ArmyListChatView: View {
    @Binding var list: ArmyListDocument
    let catalog: ArmyCatalog
    let store: ArmyListStore

    @StateObject private var runtime: ArmyListChatRuntime
    @State private var draft = ""
    /// A few words of theme the build/fill prompts fold into list generation.
    @State private var theme = ""
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
                id: "build-list",
                title: "Build list",
                text: ArmyListChatPromptComposer.buildPrompt(theme: theme)
            ),
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
                text: ArmyListChatPromptComposer.fillPointsPrompt(theme: theme)
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
                themeField
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

    /// Optional theme words that Build list and Fill points fold into the
    /// generation prompt (for example "veteran survivors" or "night raiders").
    private var themeField: some View {
        HStack(spacing: 8) {
            Image(systemName: "paintpalette")
                .font(.caption)
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            TextField("Theme for Build / Fill (optional)", text: $theme)
                .font(.caption)
                .textInputAutocapitalization(.words)
                .submitLabel(.done)
                .accessibilityLabel("List theme")
                .accessibilityIdentifier("armyListChatTheme")
            if !theme.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
                Button {
                    theme = ""
                } label: {
                    Image(systemName: "xmark.circle.fill")
                        .foregroundStyle(.secondary)
                }
                .buttonStyle(.plain)
                .accessibilityLabel("Clear theme")
                .accessibilityIdentifier("armyListChatThemeClear")
            }
        }
        .padding(.horizontal)
        .padding(.top, 8)
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

/// Builds the Build list / Fill points prompts, folding in optional theme words.
///
/// Kept separate from the view so prompt composition is unit-testable.
enum ArmyListChatPromptComposer {
    /// A trailing clause instructing the model to honor the user's theme, or
    /// empty when no theme was given.
    static func themeClause(_ theme: String) -> String {
        let trimmed = theme.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return "" }
        return " Theme to honor: \(trimmed). Choose units, detachment, and army name that fit this theme."
    }

    /// From-scratch build. One `applyRosterPlan` call to avoid context blowouts.
    static func buildPrompt(theme: String) -> String {
        "Build a fresh, legal army list from scratch for this faction at the current battle size. "
            + "Call getListSummary first for the faction and points limit, use searchCatalog as needed, "
            + "then call applyRosterPlan ONCE with a full plan (battle size, detachments, units, name). "
            + "Do not loop addUnit."
            + themeClause(theme)
    }

    /// Fill remaining points on top of the existing roster.
    static func fillPointsPrompt(theme: String) -> String {
        "Fill remaining points with a thematic extension of this list. "
            + "Keep battle size and existing units. Call getListSummary, note pts remaining, "
            + "then addUnit a few fitting datasheets (check copies N/limit in searchCatalog). "
            + "Never exceed the points limit or duplicate caps. Never call setBattleSize. "
            + "Stop when remaining points are too small for another legal unit, then briefly say what you added."
            + themeClause(theme)
    }
}

/// Parses assistant Markdown into an `AttributedString` for chat bubbles.
///
/// SwiftUI `Text` ignores the block-level `presentationIntent` that
/// `AttributedString(markdown:)` produces, so parsing a multi-paragraph reply
/// with `.full` collapses every paragraph and list item onto one run with no
/// breaks. We keep block structure ourselves: split the reply into paragraphs
/// and lines, parse each line's inline markup, and rejoin with explicit
/// newlines (`\n\n` between paragraphs, `\n` within one).
enum ArmyListChatMarkdown {
    static func attributed(_ text: String) -> AttributedString {
        let normalized = insertSoftBreaks(
            text.replacingOccurrences(of: "\r\n", with: "\n")
        )
        let paragraphs = normalized
            .components(separatedBy: "\n\n")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }

        var result = AttributedString()
        for (index, paragraph) in paragraphs.enumerated() {
            if index > 0 {
                result.append(AttributedString("\n\n"))
            }
            result.append(renderParagraph(paragraph))
        }
        return result
    }

    /// When the model forgets newlines between sections, insert soft breaks so
    /// labels like `Weakness:` / `Countermeasure:` and bold headings still
    /// read as separate blocks.
    static func insertSoftBreaks(_ text: String) -> String {
        var result = text
        // `.Countermeasure:` / `.Weakness:` → period, blank line, label.
        for label in ["Weakness", "Countermeasure", "Strength", "Theme"] {
            result = result.replacingOccurrences(
                of: #"([.!?])\s*"# + label + #":"#,
                with: "$1\n\n\(label):",
                options: .regularExpression
            )
        }
        // `Tyranids:Weakness:` style faction labels jammed before Weakness.
        result = result.replacingOccurrences(
            of: #"([A-Za-z][A-Za-z0-9' -]{1,40}):\s*(Weakness:)"#,
            with: "\n\n$1:\n$2",
            options: .regularExpression
        )
        // Sentence end immediately followed by a bold heading.
        result = result.replacingOccurrences(
            of: #"([.!?])\s*(\*\*[^*\n]+\*\*)"#,
            with: "$1\n\n$2",
            options: .regularExpression
        )
        // Collapse accidental triple blank lines from overlapping rules.
        while result.contains("\n\n\n") {
            result = result.replacingOccurrences(of: "\n\n\n", with: "\n\n")
        }
        return result
    }

    private static func renderParagraph(_ paragraph: String) -> AttributedString {
        let lines = paragraph.components(separatedBy: "\n")
        var block = AttributedString()
        for (index, line) in lines.enumerated() {
            if index > 0 {
                block.append(AttributedString("\n"))
            }
            block.append(renderLine(line))
        }
        return block
    }

    private static func renderLine(_ line: String) -> AttributedString {
        let trimmed = line.trimmingCharacters(in: .whitespaces)

        // Headings: strip the leading #s and render the rest bold.
        if let heading = headingBody(trimmed) {
            var attributed = inline(heading)
            attributed.inlinePresentationIntent = .stronglyEmphasized
            return attributed
        }

        // Bullets (-, *, +) and ordered items (1.) get a stable marker so the
        // list reads as a list without relying on block presentation intent.
        if let (marker, body) = listItem(trimmed) {
            var attributed = AttributedString(marker)
            attributed.append(inline(body))
            return attributed
        }

        return inline(line)
    }

    private static func headingBody(_ line: String) -> String? {
        guard line.hasPrefix("#") else { return nil }
        let hashes = line.prefix { $0 == "#" }
        guard hashes.count <= 6 else { return nil }
        let rest = line.dropFirst(hashes.count)
        guard rest.first == " " else { return nil }
        return rest.trimmingCharacters(in: .whitespaces)
    }

    private static func listItem(_ line: String) -> (marker: String, body: String)? {
        for bullet in ["- ", "* ", "+ "] where line.hasPrefix(bullet) {
            return ("•\u{00A0}", String(line.dropFirst(bullet.count)))
        }
        // Ordered item: digits then ". "
        let digits = line.prefix { $0.isNumber }
        if !digits.isEmpty {
            let afterDigits = line.dropFirst(digits.count)
            if afterDigits.hasPrefix(". ") {
                return ("\(digits).\u{00A0}", String(afterDigits.dropFirst(2)))
            }
        }
        return nil
    }

    private static func inline(_ text: String) -> AttributedString {
        let options = AttributedString.MarkdownParsingOptions(
            interpretedSyntax: .inlineOnlyPreservingWhitespace,
            failurePolicy: .returnPartiallyParsedIfPossible
        )
        if let parsed = try? AttributedString(markdown: text, options: options) {
            return parsed
        }
        return AttributedString(text)
    }
}

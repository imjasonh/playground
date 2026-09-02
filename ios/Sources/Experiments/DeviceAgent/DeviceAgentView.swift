import SwiftUI
import UIKit

/// Chat + tool transcript + in-app browser for Device Agent.
struct DeviceAgentView: View {
    @StateObject private var runtime = AgentRuntime()
    @StateObject private var voice = AgentVoiceCapture()
    @StateObject private var liveBrowseRunner = AgentLiveBrowseSoakRunner()
    @ObservedObject private var inbox = AgentInbox.shared
    @ObservedObject private var permissions = AgentPermissionGate.shared

    @State private var draft = ""
    @State private var showBrowser = false
    @State private var voiceMode = false
    @State private var exportShareURL: URL?
    @State private var exportError: String?
    @FocusState private var promptFocused: Bool
    @Environment(\.scenePhase) private var scenePhase

    var body: some View {
        VStack(spacing: 0) {
            if liveBrowseRunner.isRunning || !liveBrowseRunner.results.isEmpty {
                liveBrowsePane
            } else if runtime.isModelAvailable {
                statusBar
                transcriptList
                    .frame(maxHeight: showBrowser ? 220 : .infinity)
                if showBrowser {
                    browserPane
                        .frame(minHeight: 280)
                        .layoutPriority(1)
                        .transition(.move(edge: .bottom))
                }
                if voiceMode && !showBrowser {
                    voiceBar
                }
                if showBrowser && !promptFocused {
                    followUpBar
                } else {
                    composer
                }
            } else {
                unavailablePane
            }
        }
        .animation(.easeInOut(duration: 0.2), value: showBrowser)
        .animation(.easeInOut(duration: 0.2), value: voiceMode)
        .animation(.easeInOut(duration: 0.2), value: promptFocused)
        .animation(.easeInOut(duration: 0.2), value: runtime.isModelAvailable)
        .animation(.easeInOut(duration: 0.2), value: liveBrowseRunner.isRunning)
        .scrollDismissesKeyboard(.interactively)
        .onAppear {
            runtime.refreshModelStatus()
            if AgentLiveBrowseSoakRunner.shouldAutostartFromLaunchArguments {
                Task {
                    await liveBrowseRunner.runAll(
                        context: runtime.context,
                        suiteTimeoutSeconds: 5 * 60
                    )
                }
            } else if runtime.isModelAvailable {
                consumeInboxIfNeeded()
            }
        }
        .onChange(of: scenePhase) { phase in
            guard phase == .active else { return }
            let wasAvailable = runtime.isModelAvailable
            runtime.refreshModelStatus()
            if runtime.isModelAvailable {
                if !wasAvailable {
                    runtime.clearTranscript()
                }
                consumeInboxIfNeeded()
            }
        }
        .onChange(of: inbox.pendingRun?.id) { _ in
            if runtime.isModelAvailable {
                consumeInboxIfNeeded()
            }
        }
        .onChange(of: runtime.context.browserURL) { url in
            if url != nil {
                openBrowserPane()
            }
        }
        .onChange(of: runtime.context.browser.url) { url in
            if url != nil {
                openBrowserPane()
                runtime.context.browserURL = url
            }
        }
        .onChange(of: runtime.context.browser.title) { title in
            if !title.isEmpty {
                runtime.context.browserTitle = title
            }
        }
        .onChange(of: permissions.prePromptDomain) { domain in
            if let domain {
                runtime.appendPermission(domain)
            }
        }
        .sheet(isPresented: Binding(
            get: { exportShareURL != nil },
            set: { if !$0 { exportShareURL = nil } }
        )) {
            if let exportShareURL {
                NavigationStack {
                    VStack(alignment: .leading, spacing: 16) {
                        Text("Share this ZIP (JSONL inside) to debug tool calls, browser replay, and AFM page-extraction failures.")
                            .font(.footnote)
                            .foregroundStyle(.secondary)
                        ShareLink(item: exportShareURL) {
                            Label("Share ZIP", systemImage: "square.and.arrow.up")
                                .frame(maxWidth: .infinity)
                        }
                        .buttonStyle(.borderedProminent)
                        .accessibilityIdentifier("deviceAgentExportShareLink")
                        Spacer()
                    }
                    .padding()
                    .navigationTitle("Export conversation")
                    .navigationBarTitleDisplayMode(.inline)
                    .toolbar {
                        ToolbarItem(placement: .cancellationAction) {
                            Button("Done") { self.exportShareURL = nil }
                        }
                    }
                }
                .presentationDetents([.medium])
            }
        }
        .alert("Export failed", isPresented: Binding(
            get: { exportError != nil },
            set: { if !$0 { exportError = nil } }
        )) {
            Button("OK", role: .cancel) { exportError = nil }
        } message: {
            Text(exportError ?? "")
        }
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("deviceAgentRoot")
    }

    private var liveBrowsePane: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Live browse soak")
                .font(.headline)
                .accessibilityIdentifier("deviceAgentLiveQueriesTitle")
            Text(liveBrowseSummaryText)
                .font(.subheadline.monospacedDigit())
                .foregroundStyle(liveBrowseRunner.allPassed ? .green : .primary)
                .accessibilityElement(children: .ignore)
                .accessibilityLabel(liveBrowseSummaryText)
                .accessibilityIdentifier("deviceAgentLiveQueriesSummary")
                .accessibilityValue(liveBrowseRunner.isRunning ? "running" : "finished")
            if liveBrowseRunner.isRunning {
                ProgressView()
                    .accessibilityIdentifier("deviceAgentLiveQueriesProgress")
            }
            if runtime.context.browser.url != nil || runtime.context.browserURL != nil {
                AgentBrowserPane(session: runtime.context.browser)
                    .frame(minHeight: 160, maxHeight: 220)
                    .clipShape(RoundedRectangle(cornerRadius: 10, style: .continuous))
                    .accessibilityIdentifier("deviceAgentLiveQueriesBrowser")
            }
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 8) {
                    ForEach(liveBrowseRunner.results) { result in
                        VStack(alignment: .leading, spacing: 2) {
                            Text("\(result.passed ? "PASS" : "FAIL") · \(result.scenario.id) · \(result.status.rawValue)")
                                .font(.caption.weight(.semibold))
                                .foregroundStyle(result.passed ? .green : .red)
                            Text(result.scenario.prompt)
                                .font(.subheadline)
                                .lineLimit(3)
                            Text(result.scenario.url)
                                .font(.caption2)
                                .foregroundStyle(.secondary)
                                .lineLimit(1)
                            Text(result.summary)
                                .font(.caption)
                                .foregroundStyle(.secondary)
                        }
                        .padding(10)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .background(Color(.secondarySystemBackground))
                        .clipShape(RoundedRectangle(cornerRadius: 10, style: .continuous))
                        .accessibilityElement(children: .combine)
                        .accessibilityLabel("\(result.passed ? "passed" : "failed") \(result.scenario.id)")
                        .accessibilityIdentifier("deviceAgentLiveQuery-\(result.scenario.id)")
                        .accessibilityValue(result.passed ? "passed" : "failed")
                    }
                }
            }
        }
        .padding()
        .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("deviceAgentLiveQueriesRoot")
        .accessibilityValue(liveBrowseRunner.isRunning ? "running" : "finished")
    }

    private var liveBrowseSummaryText: String {
        if liveBrowseRunner.summaryLine.isEmpty {
            return "Preparing \(AgentLiveBrowseCatalog.count) live browse soaks…"
        }
        return liveBrowseRunner.summaryLine
    }

    private var unavailablePane: some View {
        VStack(spacing: 16) {
            Spacer()
            Image(systemName: unavailableSymbol)
                .font(.system(size: 44))
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            if case .modelNotReady = runtime.modelGate {
                ProgressView()
                    .accessibilityIdentifier("deviceAgentModelDownloading")
            }
            Text(runtime.modelGate.title)
                .font(.title3.weight(.semibold))
                .multilineTextAlignment(.center)
                .padding(.horizontal, 24)
                .accessibilityIdentifier("deviceAgentUnavailableTitle")
            Text(runtime.modelGate.detail)
                .font(.body)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .padding(.horizontal, 24)
                .accessibilityIdentifier("deviceAgentUnavailableDetail")
            if let action = runtime.modelGate.primaryAction {
                Button(action.title) {
                    Task {
                        await runtime.performModelGateAction(action)
                    }
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("deviceAgentModelGateAction")
                .padding(.top, 4)
            }
            // Secondary Settings link while the model is downloading (download can stall).
            if case .modelNotReady = runtime.modelGate {
                Button("Open Apple Intelligence Settings") {
                    Task { await AgentAppleIntelligenceSettings.open() }
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("deviceAgentOpenIntelligenceSettings")
            }
            Spacer()
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("deviceAgentUnavailable")
    }

    private var unavailableSymbol: String {
        switch runtime.modelGate {
        case .needsAppleIntelligence:
            return "sparkles"
        case .modelNotReady:
            return "arrow.down.circle"
        case .deviceNotEligible, .unsupportedPlatform, .other, .available:
            return "globe"
        }
    }

    private var statusBar: some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text(runtime.modelGate.title)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("deviceAgentModelStatus")
                Spacer()
                Button {
                    exportConversation()
                } label: {
                    Image(systemName: "square.and.arrow.up")
                }
                .accessibilityLabel("Export conversation")
                .accessibilityIdentifier("deviceAgentExportButton")
            }
            contextMeter
            if let pre = permissions.prePromptDomain {
                Text(pre.prePrompt)
                    .font(.footnote)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("deviceAgentPermissionPrePrompt")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .padding(.horizontal)
        .padding(.vertical, 8)
    }

    private var contextMeter: some View {
        let usage = runtime.contextUsage
        let tint: Color = {
            if usage.fractionUsed >= 0.85 { return .orange }
            if usage.fractionUsed >= AgentContextBudget.compactThreshold { return .yellow }
            return Color.secondary.opacity(0.85)
        }()
        return VStack(alignment: .leading, spacing: 4) {
            HStack {
                Text("Context")
                    .font(.caption2.weight(.semibold))
                    .foregroundStyle(.secondary)
                Spacer()
                Text("\(usage.percentUsed)%")
                    .font(.caption2.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("deviceAgentContextPercent")
            }
            ProgressView(value: usage.fractionUsed, total: 1)
                .tint(tint)
                .accessibilityIdentifier("deviceAgentContextMeter")
            if usage.didCompact {
                Text("Older turns were compacted to stay under the model limit.")
                    .font(.caption2)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("deviceAgentContextCompactNote")
            }
        }
        .accessibilityElement(children: .combine)
        .accessibilityLabel(usage.accessibilityLabel)
        .accessibilityIdentifier("deviceAgentContextUsage")
    }

    private var transcriptList: some View {
        ScrollViewReader { proxy in
            ScrollView {
                let visible = runtime.transcript.filter(\.isVisibleInChat)
                if visible.isEmpty {
                    VStack(spacing: 8) {
                        Image(systemName: "cpu")
                            .font(.largeTitle)
                            .foregroundStyle(.secondary)
                            .accessibilityHidden(true)
                        Text("Ask Device Agent")
                            .font(.headline)
                        Text("Type a request or open the browser pane.")
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                            .multilineTextAlignment(.center)
                    }
                    .frame(maxWidth: .infinity)
                    .padding(.top, 48)
                    .padding(.horizontal)
                } else {
                    LazyVStack(alignment: .leading, spacing: 10) {
                        ForEach(visible) { entry in
                            transcriptRow(entry)
                                .id(entry.id)
                        }
                    }
                    .padding()
                }
            }
            .onChange(of: runtime.transcript.count) { _ in
                if let last = runtime.transcript.last(where: \.isVisibleInChat)?.id {
                    withAnimation {
                        proxy.scrollTo(last, anchor: .bottom)
                    }
                }
            }
        }
        .accessibilityIdentifier("deviceAgentTranscript")
    }

    @ViewBuilder
    private func transcriptRow(_ entry: AgentTranscriptEntry) -> some View {
        let style = style(for: entry.kind)
        VStack(alignment: .leading, spacing: 2) {
            Text(style.label)
                .font(.caption2.weight(.semibold))
                .foregroundStyle(style.color)
            Text(entry.text)
                .font(.body)
                .textSelection(.enabled)
        }
        .padding(10)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(style.color.opacity(0.08))
        .clipShape(RoundedRectangle(cornerRadius: 10, style: .continuous))
    }

    private func style(for kind: AgentTranscriptEntry.Kind) -> (label: String, color: Color) {
        switch kind {
        case .user: return ("You", .blue)
        case .assistant: return ("Agent", .primary)
        case .toolCall: return ("Tool", .purple)
        case .toolResult: return ("Result", .purple)
        case .system: return ("System", .secondary)
        case .permission: return ("Permission", .orange)
        case .pageFindings: return ("Page", .teal)
        }
    }

    private var browserPane: some View {
        VStack(spacing: 0) {
            HStack(spacing: 10) {
                Text(runtime.context.browser.title.isEmpty
                    ? (runtime.context.browserTitle.isEmpty ? "Browser" : runtime.context.browserTitle)
                    : runtime.context.browser.title)
                    .font(.caption.weight(.semibold))
                    .lineLimit(1)
                Spacer()
                if runtime.context.browser.isLoading {
                    ProgressView()
                        .scaleEffect(0.7)
                }
                if promptFocused {
                    Button("Hide keyboard") {
                        dismissKeyboard()
                    }
                    .font(.caption.weight(.semibold))
                    .accessibilityIdentifier("deviceAgentHideKeyboard")
                }
                Button("Close") {
                    dismissKeyboard()
                    showBrowser = false
                }
                .font(.caption)
            }
            .padding(.horizontal)
            .padding(.vertical, 6)
            if runtime.context.browser.url == nil && runtime.context.browserURL == nil {
                Text("Ask Device Agent to open an http(s) URL. Scraped bullets show up in the chat; the tab stays open for follow-ups.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .padding()
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
                    .background(Color(.secondarySystemBackground))
            } else {
                AgentBrowserPane(session: runtime.context.browser)
                    .background(Color(.secondarySystemBackground))
                    .simultaneousGesture(
                        TapGesture().onEnded { dismissKeyboard() }
                    )
            }
        }
        .accessibilityIdentifier("deviceAgentBrowser")
    }

    private var followUpBar: some View {
        Button {
            promptFocused = true
        } label: {
            HStack {
                Image(systemName: "text.bubble")
                Text("Ask a follow-up about this page…")
                Spacer()
            }
            .font(.body)
            .padding(.horizontal, 14)
            .padding(.vertical, 12)
            .background(Color(.secondarySystemBackground))
            .clipShape(RoundedRectangle(cornerRadius: 12, style: .continuous))
        }
        .buttonStyle(.plain)
        .padding(.horizontal)
        .padding(.vertical, 10)
        .background(.bar)
        .accessibilityIdentifier("deviceAgentFollowUpBar")
    }

    private var voiceBar: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text(voice.statusMessage)
                .font(.caption)
                .foregroundStyle(.secondary)
            if !voice.transcript.isEmpty {
                Text(voice.transcript)
                    .font(.body)
                    .padding(8)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .background(Color(.secondarySystemBackground))
                    .clipShape(RoundedRectangle(cornerRadius: 8, style: .continuous))
            }
            HStack {
                Button {
                    Task { await voice.toggle() }
                } label: {
                    Label(
                        voice.isRecording ? "Stop" : "Listen",
                        systemImage: voice.isRecording ? "stop.circle.fill" : "mic.circle.fill"
                    )
                }
                .buttonStyle(.borderedProminent)
                .tint(voice.isRecording ? .red : .accentColor)
                .accessibilityIdentifier("deviceAgentVoiceToggle")

                Button("Use as draft") {
                    draft = voice.transcript
                    voiceMode = false
                }
                .disabled(voice.transcript.isEmpty)
                .accessibilityIdentifier("deviceAgentVoiceUseDraft")
            }
        }
        .padding()
        .background(Color(.systemBackground))
    }

    private var composer: some View {
        VStack(spacing: 8) {
            HStack(spacing: 8) {
                Button {
                    voiceMode.toggle()
                    if !voiceMode { voice.stop() }
                } label: {
                    Image(systemName: voiceMode ? "mic.fill" : "mic")
                }
                .accessibilityLabel(voiceMode ? "Hide voice input" : "Show voice input")
                .accessibilityAddTraits(voiceMode ? [.isSelected] : [])
                .accessibilityIdentifier("deviceAgentVoiceModeButton")

                Button {
                    if showBrowser {
                        dismissKeyboard()
                        showBrowser = false
                    } else {
                        openBrowserPane()
                    }
                } label: {
                    Image(systemName: "globe")
                }
                .accessibilityLabel(showBrowser ? "Hide browser" : "Show browser")
                .accessibilityAddTraits(showBrowser ? [.isSelected] : [])
                .accessibilityIdentifier("deviceAgentBrowserToggle")

                TextField("Ask Device Agent…", text: $draft, axis: .vertical)
                    .lineLimit(1...4)
                    .textFieldStyle(.roundedBorder)
                    .focused($promptFocused)
                    .accessibilityLabel("Ask Device Agent")
                    .accessibilityIdentifier("deviceAgentPromptField")
                    .toolbar {
                        ToolbarItemGroup(placement: .keyboard) {
                            Spacer()
                            Button("Done") { dismissKeyboard() }
                                .accessibilityIdentifier("deviceAgentKeyboardDone")
                        }
                    }

                Button {
                    sendDraft()
                } label: {
                    Image(systemName: "arrow.up.circle.fill")
                        .font(.title2)
                }
                .disabled(draft.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty || runtime.isRunning)
                .accessibilityLabel("Send")
                .accessibilityIdentifier("deviceAgentSendButton")
            }
        }
        .padding()
        .background(.bar)
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("deviceAgentComposer")
    }

    private func openBrowserPane() {
        showBrowser = true
        dismissKeyboard()
        voiceMode = false
        voice.stop()
    }

    private func dismissKeyboard() {
        promptFocused = false
        UIApplication.shared.sendAction(
            #selector(UIResponder.resignFirstResponder),
            to: nil,
            from: nil,
            for: nil
        )
    }

    private func exportConversation() {
        do {
            exportShareURL = try runtime.writeConversationDumpFile()
        } catch {
            exportError = error.localizedDescription
        }
    }

    private func sendDraft() {
        let text: String
        if voiceMode, !voice.transcript.isEmpty, draft.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            text = voice.transcript
        } else {
            text = draft
        }
        draft = ""
        voice.stop()
        Task {
            await runtime.send(prompt: text, source: .chat)
        }
    }

    private func consumeInboxIfNeeded() {
        guard let run = inbox.consumePendingRun() else { return }
        if run.preferVoice {
            voiceMode = true
        }
        Task {
            await startPendingRun(run)
        }
    }

    /// Opens an optional seed URL in the in-app browser, then sends the resolved prompt.
    private func startPendingRun(_ run: AgentPendingRun) async {
        var pageAlreadyOpen = false
        if let url = run.browserURL {
            openBrowserPane()
            do {
                try await runtime.context.browser.open(url)
                runtime.context.browserURL = runtime.context.browser.url ?? url
                runtime.context.browserTitle = runtime.context.browser.title
                pageAlreadyOpen = true
            } catch {
                runtime.transcript.append(
                    AgentTranscriptEntry(
                        kind: .system,
                        text: "Couldn’t open \(url.absoluteString). The model can still try browserOpen."
                    )
                )
            }
        }

        let prompt = AgentPendingRun.resolvedPrompt(run, pageAlreadyOpen: pageAlreadyOpen)
        guard !prompt.isEmpty else {
            runtime.transcript.append(
                AgentTranscriptEntry(
                    kind: .system,
                    text: "Opened from \(run.source.rawValue)."
                )
            )
            return
        }
        draft = prompt
        await runtime.send(prompt: prompt, source: run.source)
    }
}

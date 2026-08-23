import SwiftUI
import UniformTypeIdentifiers
import MessageUI
import AppIntents
import UIKit

/// Chat + tool transcript + optional in-app browser for Device Agent.
struct DeviceAgentView: View {
    @StateObject private var runtime = AgentRuntime()
    @StateObject private var voice = AgentVoiceCapture()
    @ObservedObject private var inbox = AgentInbox.shared
    @ObservedObject private var permissions = AgentPermissionGate.shared
    @ObservedObject private var watches = AgentWatchStore.shared

    @State private var draft = ""
    @State private var showBrowser = false
    @State private var showImporter = false
    @State private var showSMS = false
    @State private var showMail = false
    @State private var voiceMode = false
    @State private var showWatches = false
    @State private var exportShareURL: URL?
    @State private var exportError: String?
    @FocusState private var promptFocused: Bool
    @Environment(\.scenePhase) private var scenePhase

    var body: some View {
        VStack(spacing: 0) {
            if runtime.isModelAvailable {
                statusBar
                if !(showBrowser && promptFocused) {
                    modePicker
                }
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
        .scrollDismissesKeyboard(.interactively)
        .onAppear {
            runtime.refreshModelStatus()
            if runtime.isModelAvailable {
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
        .onChange(of: runtime.context.pendingSMS) { draft in
            showSMS = draft != nil && MFMessageComposeViewController.canSendText()
        }
        .onChange(of: runtime.context.pendingMail) { draft in
            showMail = draft != nil && MFMailComposeViewController.canSendMail()
        }
        .onChange(of: permissions.prePromptDomain) { domain in
            if let domain {
                runtime.appendPermission(domain)
            }
        }
        .fileImporter(
            isPresented: $showImporter,
            allowedContentTypes: [.item, .text, .plainText, .pdf, .image, .data],
            allowsMultipleSelection: true
        ) { result in
            handleImport(result)
        }
        .confirmationDialog(
            runtime.context.pendingConfirmation?.title ?? "Confirm",
            isPresented: Binding(
                get: { runtime.context.pendingConfirmation != nil },
                set: { if !$0 { runtime.context.resolveConfirmation(false) } }
            ),
            titleVisibility: .visible
        ) {
            Button("Allow") { runtime.context.resolveConfirmation(true) }
            Button("Don’t allow", role: .cancel) { runtime.context.resolveConfirmation(false) }
        } message: {
            Text(runtime.context.pendingConfirmation?.message ?? "")
        }
        .sheet(isPresented: $showSMS) {
            if let sms = runtime.context.pendingSMS {
                AgentSMSComposer(draft: sms) {
                    runtime.context.pendingSMS = nil
                    showSMS = false
                }
            }
        }
        .sheet(isPresented: $showMail) {
            if let mail = runtime.context.pendingMail {
                AgentMailComposer(draft: mail) {
                    runtime.context.pendingMail = nil
                    showMail = false
                }
            }
        }
        .sheet(isPresented: $showWatches) {
            NavigationStack {
                DeviceAgentWatchesView(store: watches)
            }
        }
        .sheet(isPresented: Binding(
            get: { exportShareURL != nil },
            set: { if !$0 { exportShareURL = nil } }
        )) {
            if let exportShareURL {
                NavigationStack {
                    VStack(alignment: .leading, spacing: 16) {
                        Text("Share this JSON dump to debug tool calls and model replies. It includes hidden tool results.")
                            .font(.footnote)
                            .foregroundStyle(.secondary)
                        ShareLink(item: exportShareURL) {
                            Label("Share JSON", systemImage: "square.and.arrow.up")
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
            return "cpu"
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
                Button {
                    showWatches = true
                } label: {
                    Label("Watches", systemImage: "clock.arrow.2.circlepath")
                        .font(.footnote.weight(.semibold))
                }
                .accessibilityIdentifier("deviceAgentWatchesButton")
            }
            if watches.needsAutomationNudge {
                Button {
                    showWatches = true
                } label: {
                    Text(watches.isAutomaticCheckStale
                        ? "Automatic checks look stale — recreate your Shortcuts Automation."
                        : "Set up a repeating Shortcuts Automation so watches can wake Device Agent.")
                        .font(.caption)
                        .foregroundStyle(.orange)
                        .multilineTextAlignment(.leading)
                }
                .accessibilityIdentifier("deviceAgentAutomationNudge")
            } else if !watches.watches.isEmpty {
                Text(watches.lastAutomaticCheckSummary)
                    .font(.caption2)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("deviceAgentLastAutomaticCheck")
            }
            if let pre = permissions.prePromptDomain {
                Text(pre.prePrompt)
                    .font(.footnote)
                    .foregroundStyle(.orange)
                    .accessibilityIdentifier("deviceAgentPermissionPrePrompt")
            }
            if !inbox.attachments.isEmpty {
                Text("Inbox: \(inbox.attachments.map(\.filename).joined(separator: ", "))")
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .lineLimit(2)
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .padding(.horizontal)
        .padding(.vertical, 8)
    }

    private var modePicker: some View {
        VStack(alignment: .leading, spacing: 6) {
            Picker(
                "Mode",
                selection: Binding(
                    get: { runtime.context.mode },
                    set: { runtime.context.mode = $0 }
                )
            ) {
                ForEach(AgentMode.allCases) { mode in
                    Text(mode.title).tag(mode)
                }
            }
            .pickerStyle(.segmented)
            .accessibilityIdentifier("deviceAgentModePicker")
            .onChange(of: runtime.context.mode) { mode in
                runtime.transcript.append(
                    AgentTranscriptEntry(kind: .system, text: "Mode → \(mode.title): \(mode.detail)")
                )
            }
            Text(runtime.context.mode.detail)
                .font(.caption2)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("deviceAgentModeDetail")
        }
        .padding(.horizontal)
    }

    private var transcriptList: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 10) {
                    ForEach(runtime.transcript.filter(\.isVisibleInChat)) { entry in
                        transcriptRow(entry)
                            .id(entry.id)
                    }
                }
                .padding()
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
        case .confirmation: return ("Confirm", .red)
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
                    showImporter = true
                } label: {
                    Image(systemName: "paperclip")
                }
                .accessibilityIdentifier("deviceAgentAttachButton")

                Button {
                    voiceMode.toggle()
                    if !voiceMode { voice.stop() }
                } label: {
                    Image(systemName: voiceMode ? "mic.fill" : "mic")
                }
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
        if runtime.context.mode == .observe {
            runtime.context.mode = .browse
        }
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
        runtime.context.mode = run.mode
        if run.preferVoice {
            voiceMode = true
        }
        if !run.prompt.isEmpty {
            draft = run.prompt
            Task {
                await runtime.send(prompt: run.prompt, source: run.source)
            }
        } else {
            runtime.transcript.append(
                AgentTranscriptEntry(
                    kind: .system,
                    text: "Opened from \(run.source.rawValue) with \(run.attachmentIDs.count) attachment id(s)."
                )
            )
        }
    }

    private func handleImport(_ result: Result<[URL], Error>) {
        switch result {
        case .failure(let error):
            runtime.transcript.append(
                AgentTranscriptEntry(kind: .system, text: "Attach failed: \(error.localizedDescription)")
            )
        case .success(let urls):
            for url in urls {
                do {
                    let attachment = try inbox.importFile(from: url)
                    runtime.transcript.append(
                        AgentTranscriptEntry(
                            kind: .system,
                            text: "Attached \(attachment.filename) (\(attachment.byteCount) bytes)."
                        )
                    )
                } catch {
                    runtime.transcript.append(
                        AgentTranscriptEntry(kind: .system, text: "Could not import \(url.lastPathComponent).")
                    )
                }
            }
        }
    }
}

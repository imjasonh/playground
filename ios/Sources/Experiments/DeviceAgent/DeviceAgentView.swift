import SwiftUI
import UniformTypeIdentifiers
import MessageUI

/// Chat + tool transcript + optional in-app browser for Device Agent.
struct DeviceAgentView: View {
    @StateObject private var runtime = AgentRuntime()
    @StateObject private var voice = AgentVoiceCapture()
    @ObservedObject private var inbox = AgentInbox.shared
    @ObservedObject private var permissions = AgentPermissionGate.shared

    @State private var draft = ""
    @State private var showBrowser = false
    @State private var showImporter = false
    @State private var showSMS = false
    @State private var showMail = false
    @State private var voiceMode = false

    var body: some View {
        VStack(spacing: 0) {
            statusBar
            modePicker
            transcriptList
            if showBrowser {
                browserPane
                    .frame(height: 220)
                    .transition(.move(edge: .bottom))
            }
            if voiceMode {
                voiceBar
            }
            composer
        }
        .animation(.easeInOut(duration: 0.2), value: showBrowser)
        .animation(.easeInOut(duration: 0.2), value: voiceMode)
        .onAppear {
            consumeInboxIfNeeded()
        }
        .onChange(of: inbox.pendingRun?.id) { _ in
            consumeInboxIfNeeded()
        }
        .onChange(of: runtime.context.browserURL) { url in
            if url != nil {
                showBrowser = true
                runtime.context.mode = runtime.context.mode == .observe ? .browse : runtime.context.mode
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
        .accessibilityIdentifier("deviceAgentRoot")
    }

    private var statusBar: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text(runtime.modelStatusText)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("deviceAgentModelStatus")
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
        Picker("Mode", selection: $runtime.context.mode) {
            ForEach(AgentMode.allCases) { mode in
                Text(mode.title).tag(mode)
            }
        }
        .pickerStyle(.segmented)
        .padding(.horizontal)
        .accessibilityIdentifier("deviceAgentModePicker")
        .onChange(of: runtime.context.mode) { mode in
            runtime.transcript.append(
                AgentTranscriptEntry(kind: .system, text: "Mode → \(mode.title): \(mode.detail)")
            )
        }
    }

    private var transcriptList: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 10) {
                    ForEach(runtime.transcript) { entry in
                        transcriptRow(entry)
                            .id(entry.id)
                    }
                }
                .padding()
            }
            .onChange(of: runtime.transcript.count) { _ in
                if let last = runtime.transcript.last?.id {
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
        }
    }

    private var browserPane: some View {
        VStack(spacing: 0) {
            HStack {
                Text(runtime.context.browserTitle.isEmpty ? "Browser" : runtime.context.browserTitle)
                    .font(.caption.weight(.semibold))
                Spacer()
                Button("Close") { showBrowser = false }
                    .font(.caption)
            }
            .padding(.horizontal)
            .padding(.vertical, 6)
            AgentBrowserPane(url: runtime.context.browserURL)
                .background(Color(.secondarySystemBackground))
        }
        .accessibilityIdentifier("deviceAgentBrowser")
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
                    showBrowser.toggle()
                    if showBrowser && runtime.context.browserURL == nil {
                        _ = AgentToolExecutor.browserLoadDemo(context: runtime.context)
                    }
                } label: {
                    Image(systemName: "globe")
                }
                .accessibilityIdentifier("deviceAgentBrowserToggle")

                TextField("Ask Device Agent…", text: $draft, axis: .vertical)
                    .lineLimit(1...4)
                    .textFieldStyle(.roundedBorder)
                    .accessibilityIdentifier("deviceAgentPromptField")

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

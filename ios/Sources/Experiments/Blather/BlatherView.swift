import SwiftUI

/// Topic field, transport, redirect, and saved-audio list for Blather.
struct BlatherView: View {
    @Environment(\.scenePhase) private var scenePhase
    @StateObject private var session = BlatherSession.live()
    @State private var topic = ""
    @State private var direction = ""
    @State private var showLibrary = false
    @State private var pendingDelete: BlatherEpisodeSummary?

    var body: some View {
        Group {
            if showLibrary {
                library
            } else if session.mode == .idle {
                composer
            } else {
                player
            }
        }
        .navigationTitle(showLibrary ? "Saved" : "Blather")
        .navigationBarBackButtonHidden(showLibrary)
        .toolbar {
            if showLibrary {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Player") { showLibrary = false }
                        .accessibilityIdentifier("blatherPlayerButton")
                }
            } else {
                ToolbarItem(placement: .topBarLeading) {
                    if session.mode != .idle {
                        Button("New topic") { session.finish() }
                            .accessibilityIdentifier("blatherNewTopicButton")
                    }
                }
                ToolbarItem(placement: .topBarTrailing) {
                    Button {
                        showLibrary = true
                    } label: {
                        Image(systemName: "clock")
                    }
                    .accessibilityLabel("Saved audio")
                    .accessibilityIdentifier("blatherSavedButton")
                }
            }
        }
        .accessibilityIdentifier("blatherRoot")
        .task { session.refresh() }
        .onDisappear { session.shutdown() }
        .onChange(of: scenePhase) { _, phase in
            if phase == .active {
                session.refresh()
            }
        }
        .onChange(of: session.mode) { _, mode in
            if mode == .idle {
                topic = ""
                direction = ""
            }
        }
    }

    @ViewBuilder
    private var composer: some View {
        if session.modelGate.isAvailable {
            ScrollView {
                VStack(alignment: .leading, spacing: 16) {
                    TextField("Topic", text: $topic, axis: .vertical)
                        .lineLimit(2...6)
                        .textFieldStyle(.roundedBorder)
                        .submitLabel(.go)
                        .onSubmit(start)
                        .accessibilityIdentifier("blatherTopicField")
                    Button(action: start) {
                        Label("Start", systemImage: "play.fill")
                            .frame(maxWidth: .infinity, minHeight: 44)
                    }
                    .buttonStyle(.borderedProminent)
                    .disabled(topic.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty || session.isGenerating)
                    .accessibilityIdentifier("blatherStartButton")
                }
                .padding()
            }
            .accessibilityIdentifier("blatherComposer")
        } else {
            ContentUnavailableView {
                Label(session.modelGate.title, systemImage: "sparkles")
            } description: {
                Text(session.modelGate.detail)
            } actions: {
                if let action = session.modelGate.primaryAction {
                    Button(action.title) {
                        Task { await session.performModelGateAction(action) }
                    }
                    .accessibilityIdentifier("blatherModelGateAction")
                }
            }
            .accessibilityIdentifier("blatherModelGate")
        }
    }

    private var player: some View {
        ScrollViewReader { proxy in
            ScrollView {
                VStack(alignment: .leading, spacing: 16) {
                    if let episode = session.episode {
                        Text(episode.topic)
                            .font(.headline)
                            .frame(maxWidth: .infinity, alignment: .leading)
                        playheadLabel
                        statusBlock
                        transcript(episode)
                    }
                }
                .padding()
            }
            .onChange(of: session.currentSegmentIndex) { _, index in
                guard let episode = session.episode, let index, episode.segments.indices.contains(index) else {
                    return
                }
                withAnimation {
                    proxy.scrollTo(episode.segments[index].id, anchor: .center)
                }
            }
        }
        .safeAreaInset(edge: .bottom) {
            controls
        }
        .accessibilityIdentifier("blatherPlayer")
    }

    private var playheadLabel: some View {
        Text("\(BlatherClock.label(session.playhead)) / \(BlatherClock.label(session.audibleDuration))")
            .font(.subheadline.monospacedDigit())
            .foregroundStyle(.secondary)
            .accessibilityLabel("Elapsed")
            .accessibilityValue("\(BlatherClock.label(session.playhead)) of \(BlatherClock.label(session.audibleDuration))")
            .accessibilityIdentifier("blatherPlayhead")
    }

    @ViewBuilder
    private var statusBlock: some View {
        if session.isGenerating {
            HStack(spacing: 8) {
                ProgressView()
                Text(session.hasAudio ? "Writing more audio" : "Writing audio")
                    .font(.subheadline)
                    .foregroundStyle(.secondary)
            }
            .accessibilityIdentifier("blatherWriting")
        }
        if session.didCompact {
            Text("Shortened earlier context to keep going.")
                .font(.footnote)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("blatherCompactNote")
        }
        if let errorMessage = session.errorMessage {
            VStack(alignment: .leading, spacing: 8) {
                Label(errorMessage, systemImage: "exclamationmark.triangle")
                    .font(.subheadline)
                    .foregroundStyle(.red)
                    .accessibilityIdentifier("blatherError")
                Button("Try again") {
                    Task { await session.retry() }
                }
                .accessibilityIdentifier("blatherRetryButton")
            }
        }
    }

    private func transcript(_ episode: BlatherEpisode) -> some View {
        LazyVStack(alignment: .leading, spacing: 16) {
            ForEach(Array(episode.segments.enumerated()), id: \.element.id) { index, segment in
                let isCurrent = index == session.currentSegmentIndex
                Text(segment.text)
                    .font(.body)
                    .foregroundStyle(isCurrent ? Color.primary : Color.secondary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .textSelection(.enabled)
                    .id(segment.id)
                    .accessibilityAddTraits(isCurrent ? .isSelected : [])
            }
        }
        .accessibilityIdentifier("blatherTranscript")
    }

    private var controls: some View {
        VStack(alignment: .leading, spacing: 12) {
            if canRedirect {
                HStack(alignment: .bottom, spacing: 8) {
                    TextField("Direction", text: $direction, axis: .vertical)
                        .lineLimit(1...3)
                        .textFieldStyle(.roundedBorder)
                        .accessibilityIdentifier("blatherDirectionField")
                    Button("Redirect") {
                        let text = direction
                        direction = ""
                        Task { await session.redirect(text) }
                    }
                    .buttonStyle(.borderedProminent)
                    .disabled(direction.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
                    .accessibilityIdentifier("blatherRedirectButton")
                }
            }
            if session.mode == .replay, session.modelGate.isAvailable {
                Button("Continue") {
                    Task { await session.continueTalking() }
                }
                .buttonStyle(.bordered)
                .frame(maxWidth: .infinity, minHeight: 44)
                .accessibilityIdentifier("blatherContinueButton")
            }
            HStack {
                Button {
                    session.skip(by: -BlatherTimeline.skipStep)
                } label: {
                    Image(systemName: "gobackward.10")
                        .font(.title2)
                        .frame(minWidth: 44, minHeight: 44)
                }
                .accessibilityLabel("Back 10 seconds")
                .accessibilityIdentifier("blatherSkipBackButton")
                .disabled(!session.hasAudio)
                Spacer()
                Button {
                    if session.isPlaying {
                        session.pause()
                    } else {
                        session.resume()
                    }
                } label: {
                    Image(systemName: session.isPlaying ? "pause.fill" : "play.fill")
                        .font(.title2)
                        .frame(minWidth: 64, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityLabel(session.isPlaying ? "Pause" : "Play")
                .accessibilityIdentifier("blatherPlayPauseButton")
                .disabled(!session.hasAudio)
                Spacer()
                Button {
                    session.skip(by: BlatherTimeline.skipStep)
                } label: {
                    Image(systemName: "goforward.10")
                        .font(.title2)
                        .frame(minWidth: 44, minHeight: 44)
                }
                .accessibilityLabel("Forward 10 seconds")
                .accessibilityIdentifier("blatherSkipForwardButton")
                .disabled(!session.hasAudio)
            }
        }
        .padding()
        .background(.bar)
    }

    private var canRedirect: Bool {
        session.modelGate.isAvailable
            && session.hasAudio
            && !session.isPlaying
            && (session.mode == .live || session.mode == .replay)
    }

    private var library: some View {
        List {
            if session.saved.isEmpty {
                ContentUnavailableView(
                    "No saved audio",
                    systemImage: "waveform",
                    description: Text("Start a topic and the audio stays on this device.")
                )
            } else {
                ForEach(session.saved) { item in
                    Button {
                        session.replay(id: item.id)
                        showLibrary = false
                    } label: {
                        VStack(alignment: .leading, spacing: 4) {
                            Text(item.topic)
                                .font(.headline)
                                .foregroundStyle(.primary)
                            Text("\(BlatherClock.label(item.duration)) · \(item.updatedAt.formatted(date: .abbreviated, time: .shortened))")
                                .font(.subheadline)
                                .foregroundStyle(.secondary)
                        }
                        .frame(maxWidth: .infinity, alignment: .leading)
                    }
                    .accessibilityLabel(item.topic)
                    .accessibilityValue("\(BlatherClock.label(item.duration)), \(item.updatedAt.formatted(date: .abbreviated, time: .shortened))")
                    .accessibilityIdentifier("blatherSaved-\(item.id.uuidString)")
                    .swipeActions {
                        Button("Delete", role: .destructive) {
                            pendingDelete = item
                        }
                    }
                }
            }
        }
        .listStyle(.insetGrouped)
        .accessibilityIdentifier("blatherSavedList")
        .confirmationDialog(
            "Delete this audio?",
            isPresented: Binding(
                get: { pendingDelete != nil },
                set: { if !$0 { pendingDelete = nil } }
            ),
            titleVisibility: .visible,
            presenting: pendingDelete
        ) { item in
            Button("Delete", role: .destructive) {
                session.delete(id: item.id)
                pendingDelete = nil
            }
            Button("Cancel", role: .cancel) {
                pendingDelete = nil
            }
        } message: { item in
            Text(item.topic)
        }
    }

    private func start() {
        let text = topic
        Task { await session.start(topic: text) }
    }
}

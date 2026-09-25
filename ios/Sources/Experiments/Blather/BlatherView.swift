import SwiftUI

/// Show page, player, and new-episode form for Blather.
struct BlatherView: View {
    @Environment(\.scenePhase) private var scenePhase
    @StateObject private var session = BlatherSession.live()
    @State private var topic = ""
    @State private var direction = ""
    @State private var showComposer = false
    @State private var showPlayer = false
    @State private var pendingDelete: BlatherEpisodeSummary?

    var body: some View {
        ZStack {
            BlatherShowPage(
                session: session,
                showPlayer: $showPlayer,
                pendingDelete: $pendingDelete
            )
            if showComposer {
                BlatherComposer(session: session, topic: $topic, start: start)
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
                    .background(Color(.systemBackground).ignoresSafeArea())
            }
            if showPlayer, session.episode != nil {
                BlatherPlayer(session: session, showPlayer: $showPlayer, direction: $direction)
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
                    .background(Color(.systemBackground).ignoresSafeArea())
                    .transition(.move(edge: .bottom))
            }
        }
        .animation(.easeInOut(duration: 0.25), value: showPlayer)
        .safeAreaInset(edge: .bottom) {
            if session.episode != nil, !showPlayer {
                BlatherMiniPlayer(session: session, showPlayer: $showPlayer)
            }
        }
        .navigationTitle(showComposer ? "New episode" : "Blather")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar(showPlayer ? .hidden : .visible, for: .navigationBar)
        .toolbar {
            if showComposer {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Cancel") { showComposer = false }
                        .accessibilityIdentifier("blatherCancelEpisodeButton")
                }
            } else if !showPlayer {
                ToolbarItem(placement: .primaryAction) {
                    Button("New episode") { showComposer = true }
                        .accessibilityIdentifier("blatherNewEpisodeButton")
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
            if mode == .live {
                showComposer = false
                showPlayer = true
            }
            if mode == .idle {
                showPlayer = false
                topic = ""
                direction = ""
            }
        }
        .confirmationDialog(
            "Delete this episode?",
            isPresented: deletePresented,
            titleVisibility: .visible
        ) {
            Button("Delete", role: .destructive) {
                if let item = pendingDelete {
                    session.delete(id: item.id)
                }
                pendingDelete = nil
            }
            Button("Cancel", role: .cancel) {
                pendingDelete = nil
            }
        } message: {
            Text(pendingDelete?.topic ?? "")
        }
    }

    private var deletePresented: Binding<Bool> {
        Binding(
            get: { pendingDelete != nil },
            set: { if !$0 { pendingDelete = nil } }
        )
    }

    private func start() {
        let text = topic
        Task { await session.start(topic: text) }
    }
}

private struct BlatherShowPage: View {
    @ObservedObject var session: BlatherSession
    @Binding var showPlayer: Bool
    @Binding var pendingDelete: BlatherEpisodeSummary?
    @ScaledMetric(relativeTo: .title) private var showSide: CGFloat = 96
    @ScaledMetric(relativeTo: .headline) private var rowSide: CGFloat = 64

    var body: some View {
        List {
            Section {
                showHeader
            }
            Section {
                if session.saved.isEmpty {
                    ContentUnavailableView(
                        "No episodes",
                        systemImage: "mic",
                        description: Text("Start an episode and it stays on this device.")
                    )
                    .listRowBackground(Color.clear)
                }
                ForEach(session.saved) { item in
                    episodeRow(item)
                }
            } header: {
                Text("Episodes")
            }
        }
        .listStyle(.insetGrouped)
        .accessibilityIdentifier("blatherSavedList")
    }

    private var showHeader: some View {
        HStack(alignment: .center, spacing: 16) {
            Image(uiImage: BlatherArtwork.showImage)
                .resizable()
                .scaledToFill()
                .frame(width: showSide, height: showSide)
                .clipShape(RoundedRectangle(cornerRadius: 12, style: .continuous))
                .accessibilityHidden(true)
            Text("Blather")
                .font(.title.bold)
                .frame(maxWidth: .infinity, alignment: .leading)
        }
        .padding(.vertical, 4)
    }

    private func episodeRow(_ item: BlatherEpisodeSummary) -> some View {
        Button {
            session.replay(id: item.id)
            showPlayer = true
        } label: {
            HStack(alignment: .center, spacing: 12) {
                BlatherCover(url: session.coverURL(for: item.id), topic: item.topic)
                    .frame(width: rowSide, height: rowSide)
                    .clipShape(RoundedRectangle(cornerRadius: 8, style: .continuous))
                    .accessibilityHidden(true)
                VStack(alignment: .leading, spacing: 4) {
                    Text(item.topic)
                        .font(.headline)
                        .foregroundStyle(.primary)
                        .multilineTextAlignment(.leading)
                        .lineLimit(2)
                    Text(Self.detail(item))
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                }
                .frame(maxWidth: .infinity, alignment: .leading)
            }
            .padding(.vertical, 4)
        }
        .accessibilityLabel(item.topic)
        .accessibilityValue(Self.detail(item))
        .accessibilityIdentifier("blatherSaved-\(item.id.uuidString)")
        .swipeActions {
            Button("Delete", role: .destructive) {
                pendingDelete = item
            }
        }
    }

    private static func detail(_ item: BlatherEpisodeSummary) -> String {
        "\(BlatherClock.label(item.duration)) · \(item.updatedAt.formatted(date: .abbreviated, time: .shortened))"
    }
}

private struct BlatherMiniPlayer: View {
    @ObservedObject var session: BlatherSession
    @Binding var showPlayer: Bool

    var body: some View {
        HStack(spacing: 12) {
            Button {
                showPlayer = true
            } label: {
                miniLabel
            }
            .accessibilityLabel(session.episode?.topic ?? "Episode")
            .accessibilityIdentifier("blatherMiniPlayer")
            BlatherSpeedControl(session: session)
            BlatherPlayPauseButton(session: session, prominent: false)
        }
        .padding(.horizontal)
        .padding(.vertical, 8)
        .background(.bar)
    }

    @ViewBuilder
    private var miniLabel: some View {
        HStack(spacing: 12) {
            if let episode = session.episode {
                BlatherCover(url: session.coverURL(for: episode.id), topic: episode.topic)
                    .frame(width: 44, height: 44)
                    .clipShape(RoundedRectangle(cornerRadius: 6, style: .continuous))
                    .accessibilityHidden(true)
                Text(episode.topic)
                    .font(.headline)
                    .lineLimit(1)
                    .frame(maxWidth: .infinity, alignment: .leading)
            }
        }
    }
}

private struct BlatherPlayer: View {
    @ObservedObject var session: BlatherSession
    @Binding var showPlayer: Bool
    @Binding var direction: String

    var body: some View {
        VStack(spacing: 0) {
            closeBar
            ScrollView {
                playerBody
                    .padding()
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
            .accessibilityIdentifier("blatherPlayer")
            BlatherTransport(session: session, direction: $direction)
        }
    }

    private var closeBar: some View {
        HStack {
            Button {
                showPlayer = false
            } label: {
                Image(systemName: "chevron.down")
                    .font(.body.weight(.semibold))
                    .frame(minWidth: 44, minHeight: 44)
            }
            .accessibilityLabel("Close")
            .accessibilityIdentifier("blatherClosePlayerButton")
            Spacer()
        }
        .padding(.horizontal, 8)
    }

    @ViewBuilder
    private var playerBody: some View {
        if let episode = session.episode {
            VStack(alignment: .leading, spacing: 16) {
                BlatherCover(url: session.coverURL(for: episode.id), topic: episode.topic)
                    .frame(maxWidth: 420)
                    .aspectRatio(1, contentMode: .fit)
                    .clipShape(RoundedRectangle(cornerRadius: 16, style: .continuous))
                    .frame(maxWidth: .infinity)
                    .accessibilityHidden(true)
                VStack(alignment: .leading, spacing: 4) {
                    Text(episode.topic)
                        .font(.title2.bold)
                        .frame(maxWidth: .infinity, alignment: .leading)
                    Text("Blather")
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                }
                BlatherStatus(session: session)
                BlatherTranscript(session: session, episode: episode)
            }
        }
    }
}

private struct BlatherTransport: View {
    @ObservedObject var session: BlatherSession
    @Binding var direction: String

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            scrubber
            HStack {
                skipButton(delta: -BlatherTimeline.skipStep, systemName: "gobackward.10", label: "Back 10 seconds", identifier: "blatherSkipBackButton")
                Spacer()
                BlatherPlayPauseButton(session: session, prominent: true)
                Spacer()
                skipButton(delta: BlatherTimeline.skipStep, systemName: "goforward.10", label: "Forward 10 seconds", identifier: "blatherSkipForwardButton")
            }
            HStack {
                Spacer()
                BlatherSpeedControl(session: session)
                Spacer()
            }
            if canRedirect {
                redirectField
            }
            if session.mode == .replay, session.modelGate.isAvailable, !session.isPlaying {
                Button("Continue") {
                    Task { await session.continueTalking() }
                }
                .buttonStyle(.bordered)
                .frame(maxWidth: .infinity, minHeight: 44)
                .accessibilityIdentifier("blatherContinueButton")
            }
        }
        .padding()
        .background(.bar)
    }

    private var scrubber: some View {
        VStack(spacing: 4) {
            Slider(
                value: Binding(
                    get: { session.playhead },
                    set: { session.seek(to: $0) }
                ),
                in: 0...max(session.audibleDuration, 0.01)
            )
            .disabled(!session.hasAudio)
            .accessibilityLabel("Playback position")
            .accessibilityValue("\(BlatherClock.label(session.playhead)) of \(BlatherClock.label(session.audibleDuration))")
            .accessibilityIdentifier("blatherScrubber")
            HStack {
                Text(BlatherClock.label(session.playhead))
                    .accessibilityIdentifier("blatherPlayhead")
                Spacer()
                Text("−\(BlatherClock.label(max(0, session.audibleDuration - session.playhead)))")
                    .accessibilityLabel("Remaining")
                    .accessibilityValue(BlatherClock.label(max(0, session.audibleDuration - session.playhead)))
            }
            .font(.caption.monospacedDigit())
            .foregroundStyle(.secondary)
        }
    }

    private var redirectField: some View {
        HStack(alignment: .bottom, spacing: 8) {
            TextField("New direction", text: $direction, axis: .vertical)
                .lineLimit(1...3)
                .textFieldStyle(.roundedBorder)
                .accessibilityIdentifier("blatherDirectionField")
            Button("Redirect") {
                let text = direction
                direction = ""
                Task { await session.redirect(text) }
            }
            .buttonStyle(.borderedProminent)
            .frame(minHeight: 44)
            .disabled(direction.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
            .accessibilityIdentifier("blatherRedirectButton")
        }
    }

    private var canRedirect: Bool {
        session.modelGate.isAvailable
            && session.hasAudio
            && !session.isPlaying
            && (session.mode == .live || session.mode == .replay)
    }

    private func skipButton(delta: TimeInterval, systemName: String, label: String, identifier: String) -> some View {
        Button {
            session.skip(by: delta)
        } label: {
            Image(systemName: systemName)
                .font(.title2)
                .frame(minWidth: 44, minHeight: 44)
        }
        .buttonStyle(.plain)
        .accessibilityLabel(label)
        .accessibilityIdentifier(identifier)
        .disabled(!session.hasAudio)
    }
}

private struct BlatherCover: View {
    var url: URL
    var topic: String

    var body: some View {
        Image(uiImage: BlatherArtwork.image(at: url, topic: topic))
            .resizable()
            .scaledToFill()
    }
}

private struct BlatherSpeedControl: View {
    @ObservedObject var session: BlatherSession

    var body: some View {
        Menu {
            Picker("Playback speed", selection: speed) {
                ForEach(BlatherSpeed.allCases) { rate in
                    Text(rate.label).tag(rate)
                }
            }
        } label: {
            Text(session.speed.label)
                .font(.body.monospacedDigit())
                .frame(minWidth: 72, minHeight: 44)
        }
        .buttonStyle(.bordered)
        .accessibilityLabel("Playback speed")
        .accessibilityValue(session.speed.label)
        .accessibilityIdentifier("blatherSpeedButton")
    }

    private var speed: Binding<BlatherSpeed> {
        Binding(get: { session.speed }, set: { session.setSpeed($0) })
    }
}

private struct BlatherPlayPauseButton: View {
    @ObservedObject var session: BlatherSession
    var prominent: Bool

    var body: some View {
        if prominent {
            playButton
                .buttonStyle(.borderedProminent)
                .buttonBorderShape(.circle)
        } else {
            playButton
                .buttonStyle(.plain)
        }
    }

    private var playButton: some View {
        Button(action: toggle) {
            Image(systemName: session.isPlaying ? "pause.fill" : "play.fill")
                .font(prominent ? .title : .title3)
                .frame(minWidth: prominent ? 64 : 44, minHeight: prominent ? 64 : 44)
        }
        .accessibilityLabel(session.isPlaying ? "Pause" : "Play")
        .accessibilityIdentifier("blatherPlayPauseButton")
        .disabled(!session.hasAudio)
    }

    private func toggle() {
        if session.isPlaying {
            session.pause()
        } else {
            session.resume()
        }
    }
}

private struct BlatherStatus: View {
    @ObservedObject var session: BlatherSession

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
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
}

private struct BlatherTranscript: View {
    @ObservedObject var session: BlatherSession
    var episode: BlatherEpisode

    var body: some View {
        if episode.segments.isEmpty {
            EmptyView()
        } else {
            VStack(alignment: .leading, spacing: 12) {
                Text("Transcript")
                    .font(.title3.bold)
                    .accessibilityAddTraits(.isHeader)
                LazyVStack(alignment: .leading, spacing: 16) {
                    ForEach(Array(episode.segments.enumerated()), id: \.element.id) { index, segment in
                        BlatherTranscriptLine(
                            text: segment.text,
                            isCurrent: index == session.currentSegmentIndex
                        )
                        .id(segment.id)
                    }
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("blatherTranscript")
        }
    }
}

private struct BlatherTranscriptLine: View {
    var text: String
    var isCurrent: Bool

    var body: some View {
        Text(text)
            .font(.body)
            .foregroundStyle(isCurrent ? Color.primary : Color.secondary)
            .frame(maxWidth: .infinity, alignment: .leading)
            .textSelection(.enabled)
            .modifier(CurrentSegmentTrait(isCurrent: isCurrent))
    }
}

private struct CurrentSegmentTrait: ViewModifier {
    var isCurrent: Bool

    func body(content: Content) -> some View {
        if isCurrent {
            content.accessibilityAddTraits(.isSelected)
        } else {
            content
        }
    }
}

private struct BlatherComposer: View {
    @ObservedObject var session: BlatherSession
    @Binding var topic: String
    var start: () -> Void

    var body: some View {
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
}

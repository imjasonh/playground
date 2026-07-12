import AVFoundation
import SwiftUI

/// Browse past sleep sessions and play saved snore clips.
struct SnoreSessionListView: View {
    @State private var sessions: [SleepSession] = []
    @State private var player: AVAudioPlayer?
    @State private var playingID: UUID?
    private let store = SnoreStore()

    var body: some View {
        Group {
            if sessions.isEmpty {
                Text("No saved sessions yet.")
                    .foregroundStyle(.secondary)
            } else {
                List {
                    ForEach(sessions) { session in
                        NavigationLink {
                            SnoreSessionDetailView(session: session, store: store)
                        } label: {
                            VStack(alignment: .leading, spacing: 4) {
                                Text(session.startedAt.formatted(date: .abbreviated, time: .shortened))
                                    .font(.headline)
                                Text("\(session.snoreCount) snore\(session.snoreCount == 1 ? "" : "s") · \(format(session.durationSeconds))")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                            }
                        }
                        .accessibilityIdentifier("snoreSession-\(session.id.uuidString)")
                    }
                    .onDelete(perform: delete)
                }
            }
        }
        .navigationTitle("Past sessions")
        .navigationBarTitleDisplayMode(.inline)
        .onAppear { sessions = store.loadAll() }
    }

    private func delete(at offsets: IndexSet) {
        for index in offsets {
            let session = sessions[index]
            try? store.delete(session)
        }
        sessions.remove(atOffsets: offsets)
    }

    private func format(_ t: TimeInterval) -> String {
        let total = Int(t)
        let h = total / 3600
        let m = (total % 3600) / 60
        if h > 0 { return String(format: "%dh %dm", h, m) }
        return String(format: "%dm", m)
    }
}

struct SnoreSessionDetailView: View {
    let session: SleepSession
    let store: SnoreStore

    @State private var player: AVAudioPlayer?
    @State private var playingID: UUID?

    var body: some View {
        List {
            Section {
                LabeledContent("Started", value: session.startedAt.formatted(date: .abbreviated, time: .shortened))
                LabeledContent("Duration", value: format(session.durationSeconds))
                LabeledContent("Snores", value: "\(session.snoreCount)")
            }
            Section("Clips") {
                if session.events.isEmpty {
                    Text("No clips in this session.")
                        .foregroundStyle(.secondary)
                } else {
                    ForEach(session.events) { event in
                        HStack {
                            VStack(alignment: .leading) {
                                Text("+\(format(event.sessionOffset))")
                                    .font(.subheadline.bold().monospacedDigit())
                                Text("\(String(format: "%.1fs", event.durationSeconds)) · peak \(String(format: "%.3f", event.peakRMS))")
                                    .font(.caption2)
                                    .foregroundStyle(.secondary)
                            }
                            Spacer()
                            Button {
                                togglePlay(event)
                            } label: {
                                Image(systemName: playingID == event.id ? "pause.circle.fill" : "play.circle.fill")
                                    .font(.title2)
                            }
                            .buttonStyle(.plain)
                            .accessibilityIdentifier("playSavedClip-\(event.id.uuidString)")
                        }
                    }
                }
            }
        }
        .navigationTitle("Session")
        .navigationBarTitleDisplayMode(.inline)
        .onDisappear { stopPlayback() }
    }

    private func togglePlay(_ event: SnoreEvent) {
        if playingID == event.id {
            stopPlayback()
            return
        }
        let url = store.clipURL(sessionID: session.id, fileName: event.clipFileName)
        do {
            try AVAudioSession.sharedInstance().setCategory(.playback, mode: .default)
            try AVAudioSession.sharedInstance().setActive(true)
            let p = try AVAudioPlayer(contentsOf: url)
            p.play()
            player = p
            playingID = event.id
        } catch {
            stopPlayback()
        }
    }

    private func stopPlayback() {
        player?.stop()
        player = nil
        playingID = nil
    }

    private func format(_ t: TimeInterval) -> String {
        let total = Int(t)
        let h = total / 3600
        let m = (total % 3600) / 60
        let s = total % 60
        if h > 0 { return String(format: "%d:%02d:%02d", h, m, s) }
        return String(format: "%d:%02d", m, s)
    }
}

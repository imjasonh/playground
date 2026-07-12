import AVFoundation
import SwiftUI

/// Sleep-session UI: live level meter, start/stop, and a list of snore clips.
struct SnoreLogView: View {
    @StateObject private var monitor = SnoreMonitor()
    @State private var playingID: UUID?
    @State private var player: AVAudioPlayer?

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                meter
                stats
                sensitivitySlider

                if monitor.isRunning {
                    Button(role: .destructive) {
                        stopPlayback()
                        monitor.stop()
                    } label: {
                        Label("Stop session", systemImage: "stop.circle.fill")
                            .frame(maxWidth: .infinity)
                    }
                    .buttonStyle(.borderedProminent)
                    .accessibilityIdentifier("stopSnoreSessionButton")
                } else {
                    Button {
                        monitor.start()
                    } label: {
                        Label("Start sleep session", systemImage: "moon.zzz.fill")
                            .frame(maxWidth: .infinity)
                    }
                    .buttonStyle(.borderedProminent)
                    .accessibilityIdentifier("startSnoreSessionButton")
                }

                Text(monitor.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .accessibilityIdentifier("snoreStatusMessage")

                NavigationLink {
                    SnoreSessionListView()
                } label: {
                    Label("Past sessions", systemImage: "list.bullet.rectangle")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("pastSnoreSessionsButton")

                eventLog
                howItWorks
            }
            .padding()
        }
        .onDisappear {
            if monitor.isRunning {
                monitor.stop()
            }
            stopPlayback()
        }
    }

    private var meter: some View {
        VStack(spacing: 8) {
            GeometryReader { geo in
                ZStack(alignment: .leading) {
                    Capsule()
                        .fill(Color.secondary.opacity(0.15))
                    Capsule()
                        .fill(meterColor)
                        .frame(width: max(4, geo.size.width * CGFloat(meterFraction)))
                }
            }
            .frame(height: 14)
            .accessibilityIdentifier("snoreLevelMeter")

            HStack {
                Text("level \(String(format: "%.3f", monitor.currentRMS))")
                Spacer()
                Text("floor \(String(format: "%.3f", monitor.noiseFloor))")
            }
            .font(.caption2.monospacedDigit())
            .foregroundStyle(.secondary)
        }
    }

    private var meterFraction: Double {
        min(1, monitor.currentRMS / max(monitor.threshold * 1.5, 0.05))
    }

    private var meterColor: Color {
        monitor.currentRMS >= monitor.threshold && monitor.isRunning ? .orange : .accentColor
    }

    private var stats: some View {
        HStack {
            stat("Snores", "\(monitor.snoreCount)")
            Divider()
            stat("Time", format(monitor.elapsed))
            Divider()
            stat("Thresh", String(format: "%.3f", monitor.threshold))
        }
        .frame(maxWidth: .infinity)
        .fixedSize(horizontal: false, vertical: true)
    }

    private var sensitivitySlider: some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text("Sensitivity")
                    .font(.subheadline.bold())
                Spacer()
                Text(sensitivityLabel)
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
            }
            Slider(value: $monitor.sensitivity, in: 0...1)
                .accessibilityIdentifier("snoreSensitivitySlider")
            HStack {
                Text("Less")
                Spacer()
                Text("More")
            }
            .font(.caption2)
            .foregroundStyle(.secondary)
            Text("Drag up if quiet snores are missed; drag down if talking or room noise keeps triggering.")
                .font(.caption2)
                .foregroundStyle(.tertiary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var sensitivityLabel: String {
        let percent = Int((monitor.sensitivity * 100).rounded())
        return "\(percent)%"
    }

    private func stat(_ label: String, _ value: String) -> some View {
        VStack {
            Text(value).font(.headline).monospacedDigit()
            Text(label).font(.caption2).foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity)
    }

    private var eventLog: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("This session")
                .font(.headline)
            if monitor.events.isEmpty {
                Text("No snore clips yet. Leave the phone near the bed with this screen open (or locked).")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            } else {
                ForEach(monitor.events) { event in
                    HStack {
                        Image(systemName: "waveform")
                            .foregroundStyle(.orange)
                            .frame(width: 28)
                        VStack(alignment: .leading) {
                            Text("Snore · \(String(format: "%.1fs", event.durationSeconds))")
                                .font(.subheadline).bold()
                            Text("peak \(String(format: "%.3f", event.peakRMS)) · \(format(event.sessionOffset))")
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
                        .accessibilityIdentifier("playSnoreClip-\(event.id.uuidString)")
                    }
                    .padding(.vertical, 4)
                }
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.headline)
            Text("A few seconds of audio stay in memory. When loudness rises above the ambient floor for a beat, that clip is saved — the rest of the night is discarded. Use the sensitivity slider to match your room and snore volume. Background audio keeps listening with the screen off.")
                .font(.footnote)
                .foregroundStyle(.secondary)
            Text("Not a medical device. Level-based detection will also catch talking, traffic, and other noise.")
                .font(.caption2)
                .foregroundStyle(.tertiary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private func togglePlay(_ event: SnoreEvent) {
        if playingID == event.id {
            stopPlayback()
            return
        }
        guard let sessionID = monitor.currentSessionID ?? monitor.lastSavedSession?.id else { return }
        let url = monitor.store.clipURL(sessionID: sessionID, fileName: event.clipFileName)
        do {
            // Don't retarget the session category while monitoring — that would
            // tear down the input tap's audio session.
            if !monitor.isRunning {
                try AVAudioSession.sharedInstance().setCategory(.playback, mode: .default)
                try AVAudioSession.sharedInstance().setActive(true)
            }
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

import SwiftUI

/// Glanceable ride stats on Apple Watch: clock time, duration, distance, and
/// current speed. Data is pushed from the phone via WatchConnectivity.
struct RideMonitorWatchView: View {
    @EnvironmentObject private var receiver: RideWatchReceiver

    var body: some View {
        TimelineView(.periodic(from: .now, by: 1)) { context in
            let snapshot = receiver.snapshot
            ScrollView {
                VStack(spacing: 10) {
                    Text(context.date, style: .time)
                        .font(.title3.weight(.semibold).monospacedDigit())
                        .accessibilityIdentifier("watchClockTime")

                    if snapshot.isRiding {
                        metric(
                            label: "Duration",
                            value: liveDuration(snapshot: snapshot, now: context.date),
                            identifier: "watchDuration"
                        )
                        metric(
                            label: "Distance",
                            value: snapshot.formattedDistanceKilometers,
                            identifier: "watchDistance"
                        )
                        metric(
                            label: "Speed",
                            value: snapshot.formattedSpeedKmh,
                            identifier: "watchSpeed"
                        )
                    } else {
                        VStack(spacing: 6) {
                            Image(systemName: "bicycle")
                                .font(.largeTitle)
                            Text("No active ride")
                                .font(.headline)
                            Text("Start a ride on iPhone")
                                .font(.caption2)
                                .foregroundStyle(.secondary)
                                .multilineTextAlignment(.center)
                        }
                        .padding(.top, 8)
                        .accessibilityIdentifier("watchIdle")
                    }
                }
                .frame(maxWidth: .infinity)
                .padding(.horizontal, 4)
            }
        }
        .navigationTitle("Ride")
    }

    private func metric(label: String, value: String, identifier: String) -> some View {
        VStack(spacing: 2) {
            Text(value)
                .font(.title2.bold().monospacedDigit())
                .minimumScaleFactor(0.6)
                .accessibilityIdentifier(identifier)
            Text(label)
                .font(.caption2)
                .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity)
    }

    /// Prefer wall-clock elapsed from `startedAt` so the Watch ticks even when
    /// phone updates are sparse; fall back to the last reported duration.
    private func liveDuration(snapshot: RideLiveSnapshot, now: Date) -> String {
        guard snapshot.isRiding, snapshot.startedAt > .distantPast else {
            return snapshot.formattedDuration
        }
        let elapsed = max(snapshot.elapsedSeconds, now.timeIntervalSince(snapshot.startedAt))
        return RideLiveSnapshot.formatDuration(elapsed)
    }
}

#Preview {
    RideMonitorWatchView()
        .environmentObject(RideWatchReceiver.shared)
}

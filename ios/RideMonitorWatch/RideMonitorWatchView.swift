import SwiftUI

/// Glanceable ride stats on Apple Watch: clock time, duration, distance, and
/// current speed. Data is pushed from the phone via WatchConnectivity. While
/// a ride is active an `HKWorkoutSession` keeps this app frontmost so raising
/// the wrist returns here without hunting through the app list.
///
/// Layout is intentionally dense and non-scrolling — a 2-column grid of
/// compact cells so everything fits on a single Watch face at a glance.
struct RideMonitorWatchView: View {
    @EnvironmentObject private var receiver: RideWatchReceiver
    @EnvironmentObject private var workout: RideWatchWorkoutController

    private let columns = [
        GridItem(.flexible(), spacing: 4),
        GridItem(.flexible(), spacing: 4),
    ]

    var body: some View {
        TimelineView(.periodic(from: .now, by: 1)) { context in
            let snapshot = receiver.snapshot
            GeometryReader { geo in
                Group {
                    if snapshot.isRiding {
                        ridingContent(snapshot: snapshot, now: context.date, size: geo.size)
                    } else {
                        idleContent
                    }
                }
                .frame(width: geo.size.width, height: geo.size.height)
            }
        }
    }

    @ViewBuilder
    private func ridingContent(snapshot: RideLiveSnapshot, now: Date, size: CGSize) -> some View {
        let cells = ridingCells(snapshot: snapshot, now: now)
        // Scale value type from available height so 3–4 grid rows still fit
        // without scrolling on small Watch faces.
        let rowCount = max(1, (cells.count + 1) / 2)
        let valueSize = min(20, max(13, (size.height - 18) / CGFloat(rowCount) * 0.55))

        VStack(spacing: 2) {
            Text(now, style: .time)
                .font(.system(size: 12, weight: .semibold).monospacedDigit())
                .accessibilityIdentifier("watchClockTime")

            LazyVGrid(columns: columns, alignment: .center, spacing: 2) {
                ForEach(cells) { cell in
                    metricCell(cell, valueSize: valueSize)
                }
            }

            if let message = workout.lastErrorMessage {
                Text(message)
                    .font(.system(size: 9))
                    .foregroundStyle(.orange)
                    .lineLimit(1)
                    .minimumScaleFactor(0.7)
                    .multilineTextAlignment(.center)
            }
        }
        .padding(.horizontal, 1)
    }

    private var idleContent: some View {
        VStack(spacing: 4) {
            Image(systemName: "bicycle")
                .font(.title2)
            Text("No active ride")
                .font(.caption.weight(.semibold))
            Text("Start a ride on iPhone")
                .font(.system(size: 11))
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
        }
        .accessibilityIdentifier("watchIdle")
    }

    private func ridingCells(snapshot: RideLiveSnapshot, now: Date) -> [WatchMetricCell] {
        var cells: [WatchMetricCell] = [
            WatchMetricCell(
                id: "watchDuration",
                value: liveDuration(snapshot: snapshot, now: now),
                label: "Time"
            ),
            WatchMetricCell(
                id: "watchSpeed",
                value: String(
                    format: "%.0f",
                    RideUnits.milesPerHour(fromMetersPerSecond: snapshot.displaySpeed)
                ),
                label: "mph"
            ),
            WatchMetricCell(
                id: "watchDistance",
                value: String(
                    format: "%.2f",
                    RideUnits.miles(fromMeters: snapshot.distanceMeters)
                ),
                label: "mi"
            ),
        ]
        if let bpm = workout.activity.heartRateBPM {
            cells.append(
                WatchMetricCell(
                    id: "watchHeartRate",
                    value: String(format: "%.0f", bpm),
                    label: "bpm"
                )
            )
        }
        if let kcal = workout.activity.activeEnergyKilocalories {
            cells.append(
                WatchMetricCell(
                    id: "watchEnergy",
                    value: String(format: "%.0f", kcal),
                    label: "kcal"
                )
            )
        }
        if let rpm = workout.activity.cadenceRPM {
            cells.append(
                WatchMetricCell(
                    id: "watchCadence",
                    value: String(format: "%.0f", rpm),
                    label: "rpm"
                )
            )
        }
        if let watts = workout.activity.cyclingPowerWatts {
            cells.append(
                WatchMetricCell(
                    id: "watchPower",
                    value: String(format: "%.0f", watts),
                    label: "W"
                )
            )
        }
        return cells
    }

    private func metricCell(_ cell: WatchMetricCell, valueSize: CGFloat) -> some View {
        VStack(spacing: 0) {
            Text(cell.value)
                .font(.system(size: valueSize, weight: .bold).monospacedDigit())
                .minimumScaleFactor(0.4)
                .lineLimit(1)
                .accessibilityIdentifier(cell.id)
            Text(cell.label)
                .font(.system(size: 9, weight: .medium))
                .foregroundStyle(.secondary)
                .lineLimit(1)
                .minimumScaleFactor(0.7)
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

/// One compact cell in the Watch ride grid.
private struct WatchMetricCell: Identifiable {
    let id: String
    let value: String
    let label: String
}

#Preview {
    RideMonitorWatchView()
        .environmentObject(RideWatchReceiver.shared)
        .environmentObject(RideWatchWorkoutController.shared)
}

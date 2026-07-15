import SwiftUI
import WidgetKit
import ActivityKit

@main
struct RideMonitorWidgetBundle: WidgetBundle {
    var body: some Widget {
        RideMonitorLiveActivity()
    }
}

struct RideMonitorLiveActivity: Widget {
    var body: some WidgetConfiguration {
        ActivityConfiguration(for: RideMonitorAttributes.self) { context in
            RideLiveActivityLockScreenView(startedAt: context.attributes.startedAt, state: context.state)
                .padding(12)
                .activityBackgroundTint(Color.black.opacity(0.35))
                .activitySystemActionForegroundColor(.white)
        } dynamicIsland: { context in
            DynamicIsland {
                DynamicIslandExpandedRegion(.leading) {
                    VStack(alignment: .leading, spacing: 2) {
                        Text(context.state.formattedDistanceMiles)
                            .font(.headline.monospacedDigit())
                        Text("Distance")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                }
                DynamicIslandExpandedRegion(.trailing) {
                    VStack(alignment: .trailing, spacing: 2) {
                        Text(context.state.formattedAverageOverMaxSpeedMph)
                            .font(.headline.monospacedDigit())
                            .minimumScaleFactor(0.7)
                            .lineLimit(1)
                        Text("Avg / Max")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                }
                DynamicIslandExpandedRegion(.bottom) {
                    VStack(alignment: .leading, spacing: 6) {
                        RideLiveDurationText(startedAt: context.attributes.startedAt, state: context.state)
                            .font(.title3.monospacedDigit())
                            .multilineTextAlignment(.leading)
                        RideElevationProfileView(points: context.state.profile, lineWidth: 2)
                            .frame(height: 36)
                    }
                }
            } compactLeading: {
                Image(systemName: "bicycle")
            } compactTrailing: {
                Text(context.state.formattedDistanceMiles)
                    .font(.caption2.monospacedDigit())
                    .minimumScaleFactor(0.7)
            } minimal: {
                Image(systemName: "bicycle")
            }
        }
    }
}

/// Lock Screen / banner presentation: duration, distance, avg/max speed, and
/// the elevation profile colored by speed.
struct RideLiveActivityLockScreenView: View {
    var startedAt: Date
    var state: RideMonitorAttributes.ContentState

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack(alignment: .firstTextBaseline) {
                Label {
                    RideLiveDurationText(startedAt: startedAt, state: state)
                        .font(.title2.bold().monospacedDigit())
                        .multilineTextAlignment(.leading)
                } icon: {
                    Image(systemName: "bicycle")
                }
                Spacer()
                VStack(alignment: .trailing, spacing: 2) {
                    Text(state.formattedDistanceMiles)
                        .font(.headline.monospacedDigit())
                    Text(state.formattedAverageAndMaxSpeedMph)
                        .font(.caption.monospacedDigit())
                        .foregroundStyle(.secondary)
                        .minimumScaleFactor(0.7)
                        .lineLimit(1)
                }
            }

            RideElevationProfileView(points: state.profile)
                .frame(height: 44)

            HStack(spacing: 10) {
                legendDot(.blue, "slow")
                legendDot(.green, "easy")
                legendDot(.orange, "brisk")
                legendDot(.red, "fast")
                Spacer()
            }
            .font(.caption2)
            .foregroundStyle(.secondary)
        }
    }

    private func legendDot(_ color: Color, _ label: String) -> some View {
        HStack(spacing: 4) {
            Circle().fill(color).frame(width: 6, height: 6)
            Text(label)
        }
    }
}

/// Live ticking timer while riding; frozen duration once the ride ends so the
/// dismissed Live Activity doesn't keep counting past stop.
struct RideLiveDurationText: View {
    var startedAt: Date
    var state: RideMonitorAttributes.ContentState

    var body: some View {
        if state.isRiding {
            Text(timerInterval: startedAt...Date.distantFuture, countsDown: false)
        } else {
            Text(state.formattedDuration)
        }
    }
}

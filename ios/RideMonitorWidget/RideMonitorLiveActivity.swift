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
                        Text(context.state.formattedDistanceKilometers)
                            .font(.headline.monospacedDigit())
                        Text("Distance")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                }
                DynamicIslandExpandedRegion(.trailing) {
                    VStack(alignment: .trailing, spacing: 2) {
                        Text(context.state.formattedSpeedKmh)
                            .font(.headline.monospacedDigit())
                        Text("Speed")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                    }
                }
                DynamicIslandExpandedRegion(.bottom) {
                    VStack(alignment: .leading, spacing: 6) {
                        Text(timerInterval: context.attributes.startedAt...Date.distantFuture, countsDown: false)
                            .font(.title3.monospacedDigit())
                            .multilineTextAlignment(.leading)
                        RideElevationProfileView(points: context.state.profile, lineWidth: 2)
                            .frame(height: 36)
                    }
                }
            } compactLeading: {
                Image(systemName: "bicycle")
            } compactTrailing: {
                Text(context.state.formattedDistanceKilometers)
                    .font(.caption2.monospacedDigit())
                    .minimumScaleFactor(0.7)
            } minimal: {
                Image(systemName: "bicycle")
            }
        }
    }
}

/// Lock Screen / banner presentation: duration, distance, speed, and the
/// elevation profile colored by speed.
struct RideLiveActivityLockScreenView: View {
    var startedAt: Date
    var state: RideMonitorAttributes.ContentState

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack(alignment: .firstTextBaseline) {
                Label {
                    Text(timerInterval: startedAt...Date.distantFuture, countsDown: false)
                        .font(.title2.bold().monospacedDigit())
                        .multilineTextAlignment(.leading)
                } icon: {
                    Image(systemName: "bicycle")
                }
                Spacer()
                VStack(alignment: .trailing, spacing: 2) {
                    Text(state.formattedDistanceKilometers)
                        .font(.headline.monospacedDigit())
                    Text(state.formattedSpeedKmh)
                        .font(.caption.monospacedDigit())
                        .foregroundStyle(.secondary)
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

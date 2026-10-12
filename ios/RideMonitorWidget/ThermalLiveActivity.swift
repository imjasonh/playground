import SwiftUI
import WidgetKit
import ActivityKit

/// Compact Dynamic Island Live Activity for a non-nominal thermal state.
///
/// Compact and minimal presentations are an icon only. The Lock Screen row is
/// one line because ActivityKit still requires that surface. Updates never
/// pass an alert configuration.
struct ThermalLiveActivity: Widget {
    var body: some WidgetConfiguration {
        ActivityConfiguration(for: ThermalAttributes.self) { context in
            ThermalLiveActivityLockScreenView(state: context.state)
                .padding(12)
                .activityBackgroundTint(Color.black.opacity(0.35))
                .activitySystemActionForegroundColor(.white)
                .widgetURL(ExperimentDeepLink.url(forExperimentID: ThermalLink.experimentID))
        } dynamicIsland: { context in
            DynamicIsland {
                DynamicIslandExpandedRegion(.leading) {
                    Image(systemName: context.state.level.symbolName)
                        .symbolRenderingMode(.hierarchical)
                        .foregroundStyle(ThermalLiveActivityStyle.tint(context.state.level))
                        .accessibilityHidden(true)
                }
                DynamicIslandExpandedRegion(.center) {
                    Text(context.state.level.title)
                        .font(.headline)
                }
            } compactLeading: {
                Image(systemName: context.state.level.symbolName)
                    .symbolRenderingMode(.hierarchical)
                    .foregroundStyle(ThermalLiveActivityStyle.tint(context.state.level))
                    .accessibilityLabel(context.state.level.accessibilityLabel)
                    .widgetURL(ExperimentDeepLink.url(forExperimentID: ThermalLink.experimentID))
            } compactTrailing: {
                EmptyView()
            } minimal: {
                Image(systemName: context.state.level.symbolName)
                    .symbolRenderingMode(.hierarchical)
                    .foregroundStyle(ThermalLiveActivityStyle.tint(context.state.level))
                    .accessibilityLabel(context.state.level.accessibilityLabel)
                    .widgetURL(ExperimentDeepLink.url(forExperimentID: ThermalLink.experimentID))
            }
            .keylineTint(ThermalLiveActivityStyle.tint(context.state.level))
        }
    }
}

/// Lock Screen presentation required by ActivityKit. Icon plus the level name.
struct ThermalLiveActivityLockScreenView: View {
    var state: ThermalAttributes.ContentState

    var body: some View {
        HStack(spacing: 8) {
            Image(systemName: state.level.symbolName)
                .symbolRenderingMode(.hierarchical)
                .foregroundStyle(ThermalLiveActivityStyle.tint(state.level))
                .accessibilityHidden(true)
            Text(state.level.title)
                .font(.headline)
            Spacer()
        }
        .accessibilityElement(children: .combine)
        .accessibilityLabel(state.level.accessibilityLabel)
    }
}

enum ThermalLiveActivityStyle {
    static func tint(_ level: ThermalLevel) -> Color {
        switch level {
        case .nominal:
            return .secondary
        case .fair, .serious:
            return .orange
        case .critical:
            return .red
        }
    }
}

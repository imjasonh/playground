import ActivityKit
import SwiftUI
import WidgetKit

/// Thermal Live Activity. Compact and minimal views are an icon. The Lock
/// Screen row is one line because ActivityKit requires that surface.
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
            } compactTrailing: {
                EmptyView()
            } minimal: {
                Image(systemName: context.state.level.symbolName)
                    .symbolRenderingMode(.hierarchical)
                    .foregroundStyle(ThermalLiveActivityStyle.tint(context.state.level))
                    .accessibilityLabel(context.state.level.accessibilityLabel)
            }
            .keylineTint(ThermalLiveActivityStyle.tint(context.state.level))
        }
    }
}

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

import SwiftUI

struct ThermalView: View {
    @ObservedObject private var monitor = ThermalMonitor.shared

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 24) {
                currentState
                islandStatus
                levelGuide
                sessionHistory
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding()
        }
        .accessibilityIdentifier("thermalRoot")
        .onAppear {
            monitor.start()
        }
    }

    private var currentState: some View {
        Label(monitor.level.title, systemImage: monitor.level.symbolName)
            .font(.title)
            .symbolRenderingMode(.hierarchical)
            .foregroundStyle(tint(for: monitor.level))
            .accessibilityLabel(monitor.level.accessibilityLabel)
            .accessibilityIdentifier("thermalCurrentState")
    }

    private var islandStatus: some View {
        VStack(alignment: .leading, spacing: 8) {
            LabeledContent("Dynamic Island", value: islandStatusValue)
                .font(.body)
                .accessibilityIdentifier("thermalIslandStatus")
            Text(islandStatusDetail)
                .font(.subheadline)
                .foregroundStyle(.secondary)
        }
    }

    private var islandStatusValue: String {
        if !monitor.activitiesEnabled {
            return "Off"
        }
        if monitor.level.showsLiveActivity {
            return monitor.level.title
        }
        return "Hidden"
    }

    private var islandStatusDetail: String {
        if !monitor.activitiesEnabled {
            return "Live Activities are off for this app in Settings."
        }
        if monitor.level.showsLiveActivity {
            return "The thermometer icon is next to the camera. iOS also shows this state on the Lock Screen."
        }
        return "The island icon appears only when the state is fair, serious, or critical."
    }

    private var levelGuide: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Levels")
                .font(.headline)
            ForEach(ThermalLevel.allCases, id: \.self) { level in
                HStack(alignment: .top, spacing: 12) {
                    Image(systemName: level.symbolName)
                        .font(.title3)
                        .symbolRenderingMode(.hierarchical)
                        .foregroundStyle(tint(for: level))
                        .frame(width: 28, alignment: .center)
                        .accessibilityHidden(true)
                    VStack(alignment: .leading, spacing: 2) {
                        Text(level.title)
                            .font(.body)
                        Text(level.detail)
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                    }
                }
                .accessibilityElement(children: .combine)
                .accessibilityAddTraits(level == monitor.level ? .isSelected : [])
            }
        }
    }

    private var sessionHistory: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("This session")
                .font(.headline)
            if monitor.samples.count <= 1 {
                VStack(spacing: 8) {
                    Image(systemName: "clock")
                        .font(.largeTitle)
                        .foregroundStyle(.secondary)
                        .accessibilityHidden(true)
                    Text("No changes this session")
                        .font(.headline)
                    Text("The state is still \(monitor.level.title.lowercased()) since the app opened.")
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                        .multilineTextAlignment(.center)
                }
                .frame(maxWidth: .infinity)
                .padding(.vertical, 8)
            } else {
                ForEach(monitor.samples.reversed()) { sample in
                    HStack {
                        Label(sample.level.title, systemImage: sample.level.symbolName)
                            .symbolRenderingMode(.hierarchical)
                            .foregroundStyle(tint(for: sample.level))
                        Spacer()
                        Text(sample.at, style: .time)
                            .font(.body)
                            .foregroundStyle(.secondary)
                            .monospacedDigit()
                    }
                    .accessibilityElement(children: .combine)
                }
            }
        }
        .accessibilityIdentifier("thermalSessionHistory")
    }

    private func tint(for level: ThermalLevel) -> Color {
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

#Preview {
    NavigationStack {
        ThermalView()
    }
}

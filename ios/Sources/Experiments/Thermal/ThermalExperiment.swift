import SwiftUI

enum ThermalExperiment {
    static let experiment = Experiment(
        id: ThermalLink.experimentID,
        title: "Thermal",
        summary: "Shows a Dynamic Island icon when the phone is thermally limited.",
        icon: "thermometer.medium"
    ) {
        ThermalView()
    }
}

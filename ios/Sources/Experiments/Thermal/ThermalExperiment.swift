import SwiftUI

/// Registration entry for the Thermal experiment.
enum ThermalExperiment {
    static let experiment = Experiment(
        id: ThermalLink.experimentID,
        title: "Thermal",
        summary: "Dynamic Island icon when the phone is thermally limited.",
        icon: "thermometer.medium"
    ) {
        ThermalView()
    }
}

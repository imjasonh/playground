import SwiftUI

/// Registration entry for the Device Agent experiment.
enum DeviceAgentExperiment {
    static let experiment = Experiment(
        id: "device-agent",
        title: "Device Agent",
        summary: "On-device model that drives an in-app browser (open, snapshot, click, type).",
        icon: "globe"
    ) {
        DeviceAgentView()
    }
}

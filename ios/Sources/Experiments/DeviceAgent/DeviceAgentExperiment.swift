import SwiftUI

/// Registration entry for the Device Agent experiment.
enum DeviceAgentExperiment {
    static let experiment = Experiment(
        id: "device-agent",
        title: "Device Agent",
        summary: "On-device model + tools, Shortcuts/Siri, and scheduled watches via one Automation.",
        icon: "cpu"
    ) {
        DeviceAgentView()
    }
}

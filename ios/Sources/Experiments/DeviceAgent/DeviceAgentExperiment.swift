import SwiftUI

/// Registration entry for the Device Agent experiment.
enum DeviceAgentExperiment {
    static let experiment = Experiment(
        id: "device-agent",
        title: "Device Agent",
        summary: "On-device model drives an in-app browser; Shortcuts can ask, browse, summarize, or find.",
        icon: "globe"
    ) {
        DeviceAgentView()
    }
}

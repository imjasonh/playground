import SwiftUI

/// Registration entry for the Device Agent experiment.
enum DeviceAgentExperiment {
    static let experiment = Experiment(
        id: "device-agent",
        title: "Device Agent",
        summary: "On-device model + tools for Contacts, Maps, calendar, drafts, files, and a demo browser. Shortcuts and voice.",
        icon: "cpu"
    ) {
        DeviceAgentView()
    }
}

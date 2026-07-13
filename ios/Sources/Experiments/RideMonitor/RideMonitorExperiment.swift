import SwiftUI

/// Registration entry for the Ride Monitor experiment.
///
/// Each experiment folder owns one of these: metadata + destination live next
/// to the experiment's code. The central catalog only lists the entries.
enum RideMonitorExperiment {
    static let experiment = Experiment(
        id: "ride-monitor",
        title: "Ride Monitor",
        summary: "Detect shakes, potholes & crashes while biking — Live Activity + Watch while you ride.",
        icon: "bicycle"
    ) {
        RideMonitorView()
    }
}

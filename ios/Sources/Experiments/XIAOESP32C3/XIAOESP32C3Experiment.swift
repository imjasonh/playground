import SwiftUI

/// Registration entry for the Seeed Studio XIAO ESP32C3 profiling and OTLP telemetry experiment.
enum XIAOESP32C3Experiment {
    static let experiment = Experiment(
        id: "xiao-esp32c3",
        title: "XIAO ESP32C3",
        summary: "Profile wake-cycle phase timings, e-paper refresh cost, and battery mV over BLE advertisements, and forward to OTLP.",
        icon: "cpu"
    ) {
        XIAOESP32C3View()
    }
}

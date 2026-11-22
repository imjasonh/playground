import SwiftUI

/// Registration entry for the multi-MCU BLE telemetry, Cloud Trace profiling, and BLE OTA lab.
enum MCULabExperiment {
    static let experiment = Experiment(
        id: "mcu-lab",
        title: "MCU Lab",
        summary: "Multi-MCU BLE telemetry, Cloud Trace profiling, and BLE GATT OTA for XIAO ESP32-C3 and Waveshare 7.5″ e-Paper ESP32.",
        icon: "cpu"
    ) {
        XIAOESP32C3View()
    }
}

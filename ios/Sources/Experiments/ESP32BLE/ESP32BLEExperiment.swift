import SwiftUI

/// Registration entry for the ESP32 BLE experiment.
enum ESP32BLEExperiment {
    static let experiment = Experiment(
        id: "esp32-ble",
        title: "ESP32 BLE",
        summary: "Connect to PlaygroundBLE, send LED commands, and read status notifications.",
        icon: "antenna.radiowaves.left.and.right"
    ) {
        ESP32BLEView()
    }
}

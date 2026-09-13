import SwiftUI

/// Scan for PlaygroundBLE, send LED commands, and show status notifications.
struct ESP32BLEView: View {
    @StateObject private var controller = ESP32BLEController()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                scanControls
                deviceList
                commandPanel
                statusPanel
                logPanel
                howItWorks
            }
            .padding()
        }
        .onAppear {
            controller.start()
        }
        .onDisappear {
            controller.stop()
        }
    }

    private var availabilityBanner: some View {
        Group {
            if controller.isBluetoothUsable {
                Label(controller.availabilitySummary, systemImage: "checkmark.circle.fill")
                    .foregroundStyle(.green)
            } else {
                Label(controller.availabilitySummary, systemImage: "antenna.radiowaves.left.and.right.slash")
                    .foregroundStyle(.orange)
            }
        }
        .font(.subheadline)
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("esp32BleAvailabilityBanner")
    }

    private var scanControls: some View {
        VStack(spacing: 10) {
            if controller.phase == .connected || controller.phase == .connecting {
                Button(role: .destructive) {
                    controller.disconnect()
                } label: {
                    Label("Disconnect", systemImage: "xmark.circle.fill")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("esp32BleDisconnectButton")
            } else {
                Button {
                    controller.startScan()
                } label: {
                    Label(
                        controller.phase == .scanning ? "Scanning" : "Scan",
                        systemImage: "dot.radiowaves.left.and.right"
                    )
                    .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!controller.isBluetoothUsable)
                .accessibilityIdentifier("esp32BleScanButton")
            }

            Text(controller.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: .infinity)
                .accessibilityIdentifier("esp32BleStatusMessage")
        }
    }

    @ViewBuilder
    private var deviceList: some View {
        if controller.phase == .connected {
            Label(controller.connectedName, systemImage: "link")
                .font(.headline)
                .frame(maxWidth: .infinity, alignment: .leading)
                .accessibilityIdentifier("esp32BleConnectedName")
        } else if controller.isBluetoothUsable, controller.devices.isEmpty {
            ContentUnavailableView(
                "No devices yet",
                systemImage: "antenna.radiowaves.left.and.right",
                description: Text("Flash esp32-ble and keep the board powered. It advertises as PlaygroundBLE.")
            )
            .frame(minHeight: 160)
            .accessibilityIdentifier("esp32BleEmptyDevices")
        } else {
            VStack(alignment: .leading, spacing: 8) {
                Text("Nearby")
                    .font(.subheadline.bold())
                ForEach(controller.devices) { device in
                    Button {
                        controller.connect(to: device)
                    } label: {
                        HStack {
                            VStack(alignment: .leading, spacing: 2) {
                                Text(device.name)
                                    .font(.body)
                                Text("RSSI \(device.rssi)")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                            }
                            Spacer()
                            Image(systemName: "chevron.right")
                                .foregroundStyle(.tertiary)
                                .accessibilityHidden(true)
                        }
                        .frame(minHeight: 44)
                    }
                    .accessibilityLabel("Connect to \(device.name)")
                    .accessibilityIdentifier("esp32BleDevice-\(device.id.uuidString)")
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
        }
    }

    private var commandPanel: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Commands")
                .font(.subheadline.bold())
            HStack(spacing: 10) {
                commandButton("LED on", systemImage: "lightbulb.fill", command: .ledOn)
                commandButton("LED off", systemImage: "lightbulb", command: .ledOff)
            }
            commandButton("Stop", systemImage: "stop.fill", command: .stop)
            blinkSlider
            HStack(spacing: 8) {
                TextField("blink every 1s", text: $controller.commandDraft)
                    .textFieldStyle(.roundedBorder)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled()
                    .font(.body)
                    .accessibilityIdentifier("esp32BleCommandField")
                Button("Send") {
                    controller.sendDraft()
                }
                .buttonStyle(.bordered)
                .disabled(controller.phase != .connected)
                .frame(minHeight: 44)
                .accessibilityIdentifier("esp32BleSendDraftButton")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .disabled(controller.phase != .connected)
    }

    private var blinkSlider: some View {
        let periodMs = ESP32BLEProtocol.clampSliderPeriodMs(controller.blinkPeriodMs)
        let valueLabel = ESP32BLEProtocol.blinkPeriodLabel(periodMs)
        return VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text("Blink")
                    .font(.subheadline.bold())
                Spacer()
                Text(valueLabel)
                    .font(.subheadline.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("esp32BleBlinkValue")
            }
            Slider(
                value: Binding(
                    get: { controller.blinkPeriodMs },
                    set: { controller.updateBlinkPeriodMs($0) }
                ),
                in: Double(ESP32BLEProtocol.sliderMinBlinkMs)...Double(ESP32BLEProtocol.sliderMaxBlinkMs),
                step: Double(ESP32BLEProtocol.sliderBlinkStepMs)
            ) { editing in
                controller.blinkSliderEditingChanged(editing)
            }
            .frame(minHeight: 44)
            .accessibilityLabel("Blink speed")
            .accessibilityValue(valueLabel)
            .accessibilityIdentifier("esp32BleBlinkSlider")
        }
    }

    private func commandButton(_ title: String, systemImage: String, command: ESP32BLECommand) -> some View {
        Button {
            controller.send(command)
        } label: {
            Label(title, systemImage: systemImage)
                .frame(maxWidth: .infinity, minHeight: 44)
        }
        .buttonStyle(.bordered)
        .accessibilityIdentifier("esp32BleCommand-\(title)")
    }

    private var statusPanel: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Device status")
                .font(.subheadline.bold())
            if let status = controller.status {
                LabeledContent("LED", value: ledLabel(status))
                LabeledContent("Uptime", value: "\(status.uptimeS)s")
                LabeledContent("Last command", value: status.lastCommand.isEmpty ? "none" : status.lastCommand)
                if let heap = status.heapFree {
                    LabeledContent("Free heap", value: "\(heap) bytes")
                }
            } else {
                Text("No status yet.")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("esp32BleStatusPlaceholder")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("esp32BleStatusPanel")
    }

    private var logPanel: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Notifications")
                .font(.subheadline.bold())
            if controller.statusLog.isEmpty {
                Text("Subscribe happens after connect. New lines show here.")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("esp32BleLogPlaceholder")
            } else {
                ForEach(Array(controller.statusLog.enumerated()), id: \.offset) { _, line in
                    Text(line)
                        .font(.body.monospaced())
                        .textSelection(.enabled)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(10)
                        .background(Color.secondary.opacity(0.12), in: RoundedRectangle(cornerRadius: 10))
                }
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("esp32BleLogPanel")
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.subheadline.bold())
            Text(
                "The iPhone is a BLE central. The ESP32 is a peripheral that advertises "
                    + "service \(ESP32BLEProtocol.serviceUUIDString.lowercased()). Writes go to the "
                    + "command characteristic; status notifications come back on a second "
                    + "characteristic. Firmware lives in esp32-ble/."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
            if let build = Bundle.main.object(forInfoDictionaryKey: "CFBundleVersion") as? String {
                Text("Build \(build)")
                    .font(.caption2)
                    .foregroundStyle(.tertiary)
                    .accessibilityIdentifier("esp32BleBuildNumber")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private func ledLabel(_ status: ESP32BLEStatus) -> String {
        if status.blinkMs > 0 {
            let seconds = Double(status.blinkMs) / 1000
            let period = seconds == floor(seconds)
                ? String(format: "%.0f", seconds)
                : String(format: "%g", seconds)
            return status.ledOn ? "On, blinking every \(period)s" : "Off, blinking every \(period)s"
        }
        return status.ledOn ? "On" : "Off"
    }
}

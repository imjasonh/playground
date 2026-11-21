import SwiftUI

/// Foreground BLE telemetry collector, phase-budget dashboard, and OTLP/HTTP forwarder
/// for the Seeed Studio XIAO ESP32C3 firmware (`xiao-esp32c3/`).
struct XIAOESP32C3View: View {
    @StateObject private var controller = XIAOESP32C3Controller()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                scanControls
                metricsDashboard
                phaseBreakdownPanel
                otelForwarderPanel
                historyPanel
                howItWorks
            }
            .padding()
        }
        .navigationTitle("XIAO ESP32C3")
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
        .accessibilityIdentifier("xiaoAvailabilityBanner")
    }

    private var scanControls: some View {
        VStack(spacing: 10) {
            HStack(spacing: 10) {
                Button {
                    controller.toggleScan()
                } label: {
                    Label(
                        controller.isScanning ? "Listening" : "Listen for Bursts",
                        systemImage: controller.isScanning
                            ? "dot.radiowaves.left.and.right"
                            : "play.fill"
                    )
                    .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .disabled(!controller.isBluetoothUsable)
                .accessibilityIdentifier("xiaoListenButton")

                Button {
                    controller.injectSimulatedWake()
                } label: {
                    Label("Simulate Wake", systemImage: "waveform.path.ecg")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("xiaoSimulateWakeButton")
            }

            Text(controller.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: .infinity)
                .accessibilityIdentifier("xiaoStatusMessage")
        }
    }

    @ViewBuilder
    private var metricsDashboard: some View {
        if let sample = controller.latestSample {
            let m = sample.metrics
            VStack(alignment: .leading, spacing: 10) {
                HStack {
                    Text("Latest wake cycle")
                        .font(.subheadline.bold())
                    Spacer()
                    Text("seq \(m.seq)")
                        .font(.caption.monospaced())
                        .padding(.horizontal, 8)
                        .padding(.vertical, 3)
                        .background(Color.secondary.opacity(0.15), in: Capsule())
                        .accessibilityIdentifier("xiaoLatestSeq")
                }

                LabeledContent("Wake count", value: "#\(m.wakeCount)")
                    .accessibilityIdentifier("xiaoWakeCount")
                LabeledContent("Battery", value: "\(m.batteryMv) mV")
                    .accessibilityIdentifier("xiaoBatteryMv")
                LabeledContent("RSSI", value: "\(sample.rssi) dBm")
                    .accessibilityIdentifier("xiaoRssi")
                LabeledContent(
                    "Active awake time",
                    value: String(format: "%.1f ms", Double(m.totalActiveUs) / 1_000.0)
                )
                .accessibilityIdentifier("xiaoTotalActiveTime")
                LabeledContent("Estimated energy", value: "\(m.estimatedEnergyUj) µJ")
                    .accessibilityIdentifier("xiaoEstimatedEnergy")
                LabeledContent("E-paper refresh mode", value: m.epdRefreshModeLabel)
                    .accessibilityIdentifier("xiaoEpdMode")
                LabeledContent(
                    "Wake source",
                    value: m.isDeepSleepWake ? "Deep sleep timer" : "Cold boot / reset"
                )
            }
            .padding(12)
            .background(Color.secondary.opacity(0.1), in: RoundedRectangle(cornerRadius: 12))
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("xiaoMetricsDashboard")
        } else {
            ContentUnavailableView(
                "No telemetry bursts yet",
                systemImage: "cpu",
                description: Text("Wake a XIAO ESP32C3 running xiao-esp32c3 or tap Simulate Wake to inspect phase durations and OTLP payloads.")
            )
            .frame(minHeight: 160)
            .accessibilityIdentifier("xiaoEmptyMetrics")
        }
    }

    @ViewBuilder
    private var phaseBreakdownPanel: some View {
        if let sample = controller.latestSample {
            let m = sample.metrics
            let total = max(Double(m.totalActiveUs), 1)
            VStack(alignment: .leading, spacing: 10) {
                Text("Phase budget breakdown")
                    .font(.subheadline.bold())

                phaseRow(
                    title: "Sensor read & filter",
                    us: m.sensorUs,
                    fraction: Double(m.sensorUs) / total,
                    tint: .teal,
                    id: "xiaoPhaseSensor"
                )
                phaseRow(
                    title: "Compute & 1-bit framebuffer",
                    us: m.computeUs,
                    fraction: Double(m.computeUs) / total,
                    tint: .blue,
                    id: "xiaoPhaseCompute"
                )
                phaseRow(
                    title: "E-paper SPI & LUT refresh (\(m.epdRefreshModeLabel))",
                    us: m.epdRefreshUs,
                    fraction: Double(m.epdRefreshUs) / total,
                    tint: .purple,
                    id: "xiaoPhaseEpd"
                )
                phaseRow(
                    title: "BLE advertisement burst (prev wake)",
                    us: m.radioUs,
                    fraction: Double(m.radioUs) / total,
                    tint: .orange,
                    id: "xiaoPhaseRadio"
                )
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("xiaoPhasePanel")
        }
    }

    private func phaseRow(
        title: String,
        us: UInt32,
        fraction: Double,
        tint: Color,
        id: String
    ) -> some View {
        let pct = Int((fraction * 100).rounded())
        let formatted = XIAOESP32C3Protocol.formatDurationUs(us)
        return VStack(alignment: .leading, spacing: 4) {
            HStack {
                Text(title)
                    .font(.caption)
                Spacer()
                Text("\(formatted) (\(pct)%)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
            }
            ProgressView(value: min(max(fraction, 0), 1))
                .tint(tint)
        }
        .accessibilityElement(children: .combine)
        .accessibilityLabel(title)
        .accessibilityValue("\(formatted), \(pct) percent")
        .accessibilityIdentifier(id)
    }

    private var otelForwarderPanel: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("OpenTelemetry OTLP/HTTP forwarder")
                .font(.subheadline.bold())

            Toggle(
                "Auto-forward incoming wakes",
                isOn: Binding(
                    get: { controller.forwardingEnabled },
                    set: { controller.updateForwardingEnabled($0) }
                )
            )
            .frame(minHeight: 44)
            .accessibilityIdentifier("xiaoOtelAutoForwardToggle")

            Toggle(
                "Authorize with Apple App Attest (xiao-otel Cloud Run)",
                isOn: Binding(
                    get: { controller.useAppAttest },
                    set: { controller.updateUseAppAttest($0) }
                )
            )
            .frame(minHeight: 44)
            .accessibilityIdentifier("xiaoOtelAppAttestToggle")

            HStack(spacing: 8) {
                TextField(
                    XIAOESP32C3Protocol.defaultOtelEndpoint,
                    text: Binding(
                        get: { controller.otelEndpoint },
                        set: { controller.updateEndpoint($0) }
                    )
                )
                .textFieldStyle(.roundedBorder)
                .textInputAutocapitalization(.never)
                .autocorrectionDisabled()
                .keyboardType(.URL)
                .font(.body.monospaced())
                .accessibilityLabel("OTLP metrics endpoint URL")
                .accessibilityIdentifier("xiaoOtelEndpointField")

                Button("POST Now") {
                    controller.forwardLatestSampleNow()
                }
                .buttonStyle(.bordered)
                .disabled(controller.latestSample == nil)
                .frame(minHeight: 44)
                .accessibilityIdentifier("xiaoOtelPostNowButton")
            }

            HStack {
                Text(controller.lastForwardStatus)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("xiaoOtelStatus")
                Spacer()
                Text("Exported: \(controller.forwardedCount)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("xiaoOtelExportedCount")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("xiaoOtelPanel")
    }

    private var historyPanel: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Recent wake bursts")
                .font(.subheadline.bold())
            if controller.history.isEmpty {
                Text("Deduplicated BLE manufacturer frames appear here.")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("xiaoHistoryPlaceholder")
            } else {
                ForEach(controller.history) { sample in
                    Text("\(XIAOESP32C3Protocol.formatStatusLine(sample.metrics)) rssi=\(sample.rssi)")
                        .font(.caption.monospaced())
                        .textSelection(.enabled)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(10)
                        .background(Color.secondary.opacity(0.12), in: RoundedRectangle(cornerRadius: 10))
                }
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("xiaoHistoryPanel")
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.subheadline.bold())
            Text(
                "The XIAO ESP32C3 wakes from deep sleep, records microsecond durations for sensor "
                    + "filtering, 1-bit framebuffer rendering, e-paper SPI + LUT refresh, and the "
                    + "previous BLE TX burst into RTC slow memory (.rtc.data), and toggles GPIO 2 "
                    + "(D0) HIGH during each phase for Nordic PPK2 power correlation. It then "
                    + "broadcasts a 150 ms non-connectable BLE Manufacturer Specific Data (0xFFFF) "
                    + "packet and drops back into deep sleep. The iPhone scans with duplicates "
                    + "enabled, deduplicates frames by seq, and forwards OTLP/HTTP v1 JSON to "
                    + "your OpenTelemetry Collector. Firmware lives in xiao-esp32c3/."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }
}

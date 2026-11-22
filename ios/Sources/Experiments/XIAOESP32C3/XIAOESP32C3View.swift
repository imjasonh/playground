import SwiftUI
import UniformTypeIdentifiers

/// Foreground BLE telemetry collector, phase-budget dashboard, OTLP/HTTP forwarder,
/// and BLE GATT OTA firmware installer for the Seeed Studio XIAO ESP32C3 (`xiao-esp32c3/`).
struct XIAOESP32C3View: View {
    @StateObject private var controller = XIAOESP32C3Controller()
    @State private var isImportingFirmware = false

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                scanControls
                metricsDashboard
                phaseBreakdownPanel
                profileAndTracesPanel
                otaUpdaterPanel
                otelForwarderPanel
                historyPanel
                howItWorks
            }
            .padding()
        }
        .navigationTitle("XIAO ESP32C3")
        .fileImporter(
            isPresented: $isImportingFirmware,
            allowedContentTypes: [.data]
        ) { result in
            switch result {
            case .success(let url):
                let scoped = url.startAccessingSecurityScopedResource()
                defer {
                    if scoped { url.stopAccessingSecurityScopedResource() }
                }
                if let data = try? Data(contentsOf: url) {
                    controller.stageFirmware(data: data, name: url.lastPathComponent)
                }
            case .failure(let error):
                controller.otaStatusText = "File import failed: \(error.localizedDescription)"
            }
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

    private var profileAndTracesPanel: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Firmware profile & Cloud Trace spans")
                .font(.subheadline.bold())

            Toggle(
                "Collect detailed profile (sub-phase spans, heap/stack)",
                isOn: Binding(
                    get: { controller.collectDetailedProfile },
                    set: { controller.saveCollectDetailedProfile($0) }
                )
            )
            .frame(minHeight: 44)
            .accessibilityIdentifier("xiaoCollectProfileToggle")

            if let traceId = controller.latestTraceId {
                LabeledContent("Last trace ID") {
                    Text(String(traceId.prefix(16)) + "…")
                        .font(.caption.monospaced())
                        .textSelection(.enabled)
                }
                .accessibilityIdentifier("xiaoLastTraceId")
            }

            if let profile = controller.latestSample?.profile {
                LabeledContent("Free / min heap") {
                    Text("\(profile.freeHeapBytes / 1024) KB / \(profile.minFreeHeapBytes / 1024) KB")
                        .font(.caption.monospacedDigit())
                }
                LabeledContent("Stack high-water") {
                    Text("\(profile.stackHighWaterBytes) B")
                        .font(.caption.monospacedDigit())
                }
                LabeledContent("Active CPU cycles") {
                    Text("\(profile.cpuCycles)")
                        .font(.caption.monospacedDigit())
                }

                if !profile.spans.isEmpty {
                    let maxEnd = max(
                        Double(profile.spans.map { $0.startUs + $0.durationUs }.max() ?? 1),
                        1
                    )
                    Text("Sub-phase spans")
                        .font(.caption.bold())
                        .foregroundStyle(.secondary)
                    ForEach(profile.spans) { sp in
                        VStack(alignment: .leading, spacing: 3) {
                            HStack {
                                Text(sp.name)
                                    .font(.caption.monospaced())
                                Spacer()
                                Text(XIAOESP32C3Protocol.formatDurationUs(sp.durationUs))
                                    .font(.caption.monospacedDigit())
                                    .foregroundStyle(.secondary)
                            }
                            ProgressView(value: min(max(Double(sp.durationUs) / maxEnd, 0), 1))
                                .tint(.indigo)
                        }
                    }
                }

                if !profile.pcSamples.isEmpty {
                    Text("Top PC hotspots")
                        .font(.caption.bold())
                        .foregroundStyle(.secondary)
                    ForEach(profile.pcSamples.prefix(5)) { sample in
                        VStack(alignment: .leading, spacing: 2) {
                            HStack {
                                Text(sample.pc)
                                    .font(.caption.monospaced())
                                Spacer()
                                Text("\(sample.hits) hits")
                                    .font(.caption.monospacedDigit())
                                    .foregroundStyle(.secondary)
                            }
                            if let sym = controller.resolvedHotspots[sample.pc], !sym.displayLabel.isEmpty {
                                Text(sym.displayLabel)
                                    .font(.caption2.monospaced())
                                    .foregroundStyle(.secondary)
                                    .lineLimit(2)
                            }
                        }
                    }
                }
            } else {
                Text("Enable detailed profiling and receive or simulate a wake to inspect sub-phase spans and heap/stack stats.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
        }
        .padding(12)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 12))
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("xiaoProfilePanel")
    }

    private var otaUpdaterPanel: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Firmware OTA update over BLE")
                .font(.subheadline.bold())

            HStack(spacing: 8) {
                Button {
                    Task {
                        await controller.pullLatestFirmwareFromGHCR()
                    }
                } label: {
                    Label("Pull GHCR :latest", systemImage: "arrow.down.circle")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("xiaoOtaPullGhcrButton")

                Button {
                    isImportingFirmware = true
                } label: {
                    Label("Choose .bin", systemImage: "folder")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("xiaoOtaChooseBinButton")
            }

            if let staged = controller.stagedFirmwareData {
                LabeledContent("Staged image", value: "\(controller.stagedFirmwareName) (\(staged.count) B)")
                    .font(.caption)
                    .accessibilityIdentifier("xiaoOtaStagedName")
                LabeledContent("SHA-256", value: String(controller.stagedFirmwareSHA256.prefix(16)) + "…")
                    .font(.caption.monospaced())
                    .accessibilityIdentifier("xiaoOtaStagedSha")
            }

            if case .streaming(let written, let total) = controller.otaPhase, total > 0 {
                let fraction = Double(written) / Double(total)
                ProgressView(value: min(max(fraction, 0), 1))
                    .accessibilityLabel("OTA transfer progress")
                    .accessibilityValue("\(Int((fraction * 100).rounded())) percent")
                    .accessibilityIdentifier("xiaoOtaProgressView")
            }

            if controller.otaPhase == .armed || controller.otaPhase == .connecting || controller.otaPhase == .erasing {
                Button(role: .destructive) {
                    controller.cancelOTAUpdate()
                } label: {
                    Label("Cancel Armed OTA", systemImage: "xmark.circle.fill")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("xiaoOtaCancelButton")
            } else {
                Button {
                    controller.armOTAUpdate()
                } label: {
                    Label("Arm Update for Next Wake", systemImage: "bolt.horizontal.circle.fill")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .disabled(controller.stagedFirmwareData == nil)
                .accessibilityIdentifier("xiaoOtaArmButton")
            }

            Text(controller.otaStatusText)
                .font(.caption)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("xiaoOtaStatusText")
        }
        .padding(12)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 12))
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("xiaoOtaPanel")
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
                    + "broadcasts a 150 ms BLE Manufacturer Specific Data (0xFFFF) packet and "
                    + "drops back into deep sleep. When an OTA update is armed in this app, the "
                    + "iPhone connects during that 150 ms burst, streams the new firmware into the "
                    + "inactive OTA partition (ota_0 / ota_1), verifies the SHA-256 digest, and "
                    + "reboots the board with automatic rollback protection. Firmware lives in "
                    + "xiao-esp32c3/ and Cloud Run collector lives in xiao-otel/."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private func isOTAInProgress(_ phase: XIAOESP32C3Controller.OTAPhase) -> Bool {
        switch phase {
        case .armed, .connecting, .erasing, .streaming, .committing:
            return true
        case .idle, .completed, .failed:
            return false
        }
    }
}

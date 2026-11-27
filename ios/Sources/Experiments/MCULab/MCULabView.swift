import SwiftUI
import UniformTypeIdentifiers

/// Foreground BLE telemetry collector, phase-budget dashboard, OTLP/HTTP forwarder,
/// and BLE GATT OTA firmware installer for the MCU Lab boards (`mcu-lab/`).
struct MCULabView: View {
    @StateObject private var controller = MCULabController()
    @State private var isImportingFirmware = false
    @State private var commandCounts: [String: Int] = [:]

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                availabilityBanner
                scanControls
                appCommandsPanel
                MCULabSensePanel(controller: controller)
                MCULabPhotoFramePanel(controller: controller)
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
        .navigationTitle("MCU Lab")
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
        .accessibilityIdentifier("mcuLabAvailabilityBanner")
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
                .accessibilityIdentifier("mcuLabListenButton")

                Button {
                    controller.injectSimulatedWake()
                } label: {
                    Label("Simulate Wake", systemImage: "waveform.path.ecg")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("mcuLabSimulateWakeButton")
            }

            Text(controller.statusMessage)
                .font(.footnote)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
                .frame(maxWidth: .infinity)
                .accessibilityIdentifier("mcuLabStatusMessage")
        }
    }

    @ViewBuilder
    private var appCommandsPanel: some View {
        let deviceGroups = controller.sortedDeviceCommands
        if !deviceGroups.isEmpty || !controller.appCommandStatus.isEmpty {
            VStack(alignment: .leading, spacing: 10) {
                Text("App Controls")
                    .font(.subheadline.bold())

                ForEach(deviceGroups) { group in
                    VStack(alignment: .leading, spacing: 8) {
                        HStack {
                            Text(group.deviceName)
                                .font(.caption.bold())
                            Spacer()
                            if !group.app.isEmpty {
                                Text(group.app)
                                    .font(.caption.monospaced())
                                    .foregroundStyle(.secondary)
                            }
                        }

                        ForEach(group.commands) { cmd in
                            let countKey = "\(group.deviceId.uuidString):\(cmd.id)"
                            let defaultRuns = Int(max(1, cmd.defaultCount))
                            let runsBinding = Binding<Int>(
                                get: { commandCounts[countKey] ?? defaultRuns },
                                set: { commandCounts[countKey] = $0 }
                            )
                            let currentRuns = runsBinding.wrappedValue
                            VStack(alignment: .leading, spacing: 6) {
                                if cmd.defaultCount > 1 {
                                    Stepper(
                                        "Runs: \(currentRuns)",
                                        value: runsBinding,
                                        in: 1...Int(MCULabProtocol.maxAppCommandCount)
                                    )
                                    .font(.subheadline)
                                    .accessibilityIdentifier("mcuLabAppCmdStepper-\(cmd.id)")
                                }
                                HStack(spacing: 10) {
                                    Button {
                                        controller.armAppCommand(
                                            cmd,
                                            count: UInt16(currentRuns),
                                            deviceId: group.deviceId
                                        )
                                    } label: {
                                        Label(
                                            currentRuns > 1 ? "\(cmd.label) (×\(currentRuns))" : cmd.label,
                                            systemImage: "play.circle.fill"
                                        )
                                        .frame(maxWidth: .infinity, minHeight: 40)
                                    }
                                    .buttonStyle(.borderedProminent)
                                    .disabled(controller.otaPhase != .idle)
                                    .accessibilityIdentifier("mcuLabAppCmdButton-\(cmd.id)")

                                    if controller.pendingAppCommand?.deviceId == group.deviceId,
                                       controller.pendingAppCommand?.id == cmd.id
                                    {
                                        Button("Cancel", role: .cancel) {
                                            controller.cancelAppCommand()
                                        }
                                        .buttonStyle(.bordered)
                                        .accessibilityIdentifier("mcuLabAppCmdCancel-\(cmd.id)")
                                    }
                                }
                            }
                        }
                    }
                }

                if !controller.appCommandStatus.isEmpty {
                    Text(controller.appCommandStatus)
                        .font(.caption)
                        .foregroundStyle(.secondary)
                        .accessibilityIdentifier("mcuLabAppCmdStatus")
                }
            }
            .padding(12)
            .background(Color.secondary.opacity(0.1), in: RoundedRectangle(cornerRadius: 12))
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("mcuLabAppControlsPanel")
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
                        .accessibilityIdentifier("mcuLabLatestSeq")
                }

                LabeledContent(
                    "Board",
                    value: "\(sample.deviceName) (\(MCULabProtocol.serviceName(for: m, profile: sample.profile)))"
                )
                .accessibilityIdentifier("mcuLabBoardName")
                LabeledContent("Wake count", value: "#\(m.wakeCount)")
                    .accessibilityIdentifier("mcuLabWakeCount")
                LabeledContent("Battery", value: "\(m.batteryMv) mV")
                    .accessibilityIdentifier("mcuLabBatteryMv")
                LabeledContent("RSSI", value: "\(sample.rssi) dBm")
                    .accessibilityIdentifier("mcuLabRssi")
                LabeledContent(
                    "Active awake time",
                    value: String(format: "%.1f ms", Double(m.totalActiveUs) / 1_000.0)
                )
                .accessibilityIdentifier("mcuLabTotalActiveTime")
                LabeledContent("Estimated energy", value: "\(m.estimatedEnergyUj) µJ")
                    .accessibilityIdentifier("mcuLabEstimatedEnergy")
                LabeledContent("E-paper refresh mode", value: m.epdRefreshModeLabel)
                    .accessibilityIdentifier("mcuLabEpdMode")
                LabeledContent(
                    "Wake source",
                    value: m.isDeepSleepWake ? "Deep sleep timer" : "Cold boot / reset"
                )
            }
            .padding(12)
            .background(Color.secondary.opacity(0.1), in: RoundedRectangle(cornerRadius: 12))
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("mcuLabMetricsDashboard")
        } else {
            ContentUnavailableView(
                "No telemetry bursts yet",
                systemImage: "cpu",
                description: Text("Wake a board running mcu-lab (XIAO ESP32-C3, Waveshare 7.5″ ESP32, or XIAO ESP32-S3 Sense) or tap Simulate Wake to inspect phase durations and OTLP payloads.")
            )
            .frame(minHeight: 160)
            .accessibilityIdentifier("mcuLabEmptyMetrics")
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
                    id: "mcuLabPhaseSensor"
                )
                phaseRow(
                    title: "Compute & 1-bit framebuffer",
                    us: m.computeUs,
                    fraction: Double(m.computeUs) / total,
                    tint: .blue,
                    id: "mcuLabPhaseCompute"
                )
                phaseRow(
                    title: "E-paper SPI & LUT refresh (\(m.epdRefreshModeLabel))",
                    us: m.epdRefreshUs,
                    fraction: Double(m.epdRefreshUs) / total,
                    tint: .purple,
                    id: "mcuLabPhaseEpd"
                )
                phaseRow(
                    title: "BLE advertisement burst (prev wake)",
                    us: m.radioUs,
                    fraction: Double(m.radioUs) / total,
                    tint: .orange,
                    id: "mcuLabPhaseRadio"
                )
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .accessibilityIdentifier("mcuLabPhasePanel")
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
        let formatted = MCULabProtocol.formatDurationUs(us)
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
            .accessibilityIdentifier("mcuLabCollectProfileToggle")

            if let traceId = controller.latestTraceId {
                LabeledContent("Last trace ID") {
                    Text(String(traceId.prefix(16)) + "…")
                        .font(.caption.monospaced())
                        .textSelection(.enabled)
                }
                .accessibilityIdentifier("mcuLabLastTraceId")
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
                                Text(MCULabProtocol.formatDurationUs(sp.durationUs))
                                    .font(.caption.monospacedDigit())
                                    .foregroundStyle(.secondary)
                            }
                            ProgressView(value: min(max(Double(sp.durationUs) / maxEnd, 0), 1))
                                .tint(.indigo)
                        }
                    }
                }

                if let appMetrics = profile.metrics, !appMetrics.isEmpty {
                    Text("App metrics")
                        .font(.caption.bold())
                        .foregroundStyle(.secondary)
                    ForEach(appMetrics.prefix(10)) { m in
                        HStack {
                            Text(m.id)
                                .font(.caption2.monospaced())
                                .lineLimit(1)
                            Spacer()
                            Text(m.unit.map { "\($0.isEmpty ? "\(m.value)" : "\(m.value) \($0)")" } ?? "\(m.value)")
                                .font(.caption2.monospacedDigit())
                                .foregroundStyle(.secondary)
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
        .accessibilityIdentifier("mcuLabProfilePanel")
    }

    private var otaUpdaterPanel: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Firmware OTA update over BLE")
                .font(.subheadline.bold())

            Picker("Board", selection: $controller.selectedBoard) {
                ForEach(MCULabBoard.allCases) { board in
                    Text(board.displayName).tag(board)
                }
            }
            .pickerStyle(.menu)
            .accessibilityIdentifier("mcuLabTargetPicker")

            Picker("App", selection: $controller.selectedApp) {
                ForEach(controller.selectedBoard.compatibleApps) { app in
                    Text(app.displayName).tag(app)
                }
            }
            .pickerStyle(.menu)
            .accessibilityIdentifier("mcuLabAppPicker")

            HStack(spacing: 8) {
                Button {
                    Task {
                        await controller.pullLatestFirmwareFromGHCR()
                    }
                } label: {
                    Label("Pull latest from GHCR", systemImage: "arrow.down.circle")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("mcuLabOtaPullGhcrButton")

                Button {
                    isImportingFirmware = true
                } label: {
                    Label("Choose .bin", systemImage: "folder")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("mcuLabOtaChooseBinButton")
            }

            if controller.otaTransferKind == .firmware,
               let staged = controller.stagedFirmwareData
            {
                LabeledContent("Staged image", value: "\(controller.stagedFirmwareName) (\(staged.count) B)")
                    .font(.caption)
                    .accessibilityIdentifier("mcuLabOtaStagedName")
                LabeledContent("SHA-256", value: String(controller.stagedFirmwareSHA256.prefix(16)) + "…")
                    .font(.caption.monospaced())
                    .accessibilityIdentifier("mcuLabOtaStagedSha")
            }

            if controller.otaTransferKind == .firmware,
               case .streaming(let written, let total) = controller.otaPhase,
               total > 0
            {
                let fraction = Double(written) / Double(total)
                ProgressView(value: min(max(fraction, 0), 1))
                    .accessibilityLabel("OTA transfer progress")
                    .accessibilityValue("\(Int((fraction * 100).rounded())) percent")
                    .accessibilityIdentifier("mcuLabOtaProgressView")
            }

            if controller.otaTransferKind == .firmware, controller.otaPhase.isActive {
                Button(role: .destructive) {
                    controller.cancelOTAUpdate()
                } label: {
                    Label("Cancel OTA Update", systemImage: "xmark.circle.fill")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("mcuLabOtaCancelButton")
            } else {
                Button {
                    controller.armOTAUpdate()
                } label: {
                    Label("Arm Update for Next Wake", systemImage: "bolt.horizontal.circle.fill")
                        .frame(maxWidth: .infinity, minHeight: 44)
                }
                .buttonStyle(.borderedProminent)
                .disabled(
                    controller.otaTransferKind != .firmware
                        || controller.stagedFirmwareData == nil
                        || controller.otaPhase.isActive
                )
                .accessibilityIdentifier("mcuLabOtaArmButton")
            }

            if controller.otaTransferKind == .firmware {
                Text(controller.otaStatusText)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabOtaStatusText")
            }

            if let report = controller.lastOTAReport {
                otaReportCard(report)
            }
        }
        .padding(12)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 12))
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("mcuLabOtaPanel")
    }

    private func otaReportCard(_ report: MCULabOTAReport) -> some View {
        let totalSec = Double(report.totalMs) / 1_000.0
        let effKBps = Double(report.effectiveBytesPerSec) / 1_024.0
        let wireKBps = Double(report.wireBytesPerSec) / 1_024.0
        let energyJ = Double(report.estimatedMcuEnergyMj) / 1_000.0
        return VStack(alignment: .leading, spacing: 6) {
            HStack {
                Label(
                    report.isSuccess ? "Last OTA Performance" : "Last OTA Failed",
                    systemImage: report.isSuccess ? "speedometer" : "exclamationmark.triangle.fill"
                )
                .font(.caption.bold())
                .foregroundStyle(report.isSuccess ? Color.primary : Color.red)
                Spacer()
                Text(String(format: "%.1f s", totalSec))
                    .font(.caption.monospacedDigit().bold())
            }

            LabeledContent(
                "Throughput",
                value: String(format: "%.1f KB/s eff (%.1f KB/s wire)", effKBps, wireKBps)
            )
            .font(.caption2.monospacedDigit())

            if report.compression == .deflate {
                LabeledContent(
                    "Transfer",
                    value: "\(report.wireBytes / 1_024) KB / \(report.rawBytes / 1_024) KB (-\(report.compressionSavedPct)%, \(report.packetCount) pkts)"
                )
                .font(.caption2.monospacedDigit())
            } else {
                LabeledContent(
                    "Transfer",
                    value: "\(report.wireBytes / 1_024) KB raw (\(report.packetCount) pkts)"
                )
                .font(.caption2.monospacedDigit())
            }

            LabeledContent(
                "Phases",
                value: String(
                    format: "conn %.1fs · erase %.1fs · stream %.1fs · commit %.1fs",
                    Double(report.connectMs) / 1_000.0,
                    Double(report.eraseMs) / 1_000.0,
                    Double(report.streamMs) / 1_000.0,
                    Double(report.commitMs) / 1_000.0
                )
            )
            .font(.caption2.monospacedDigit())

            LabeledContent(
                "BLE RTT",
                value: String(format: "%.1f ms/pkt", report.avgRttMs)
            )
            .font(.caption2.monospacedDigit())

            LabeledContent("MCU energy", value: mcuBatterySummary(report, energyJ: energyJ))
                .font(.caption2.monospacedDigit())

            if let phoneSummary = phoneBatterySummary(report) {
                LabeledContent("iPhone battery", value: phoneSummary)
                    .font(.caption2.monospacedDigit())
            }
        }
        .padding(10)
        .background(Color.secondary.opacity(0.08), in: RoundedRectangle(cornerRadius: 8))
        .accessibilityIdentifier("mcuLabOtaReportCard")
    }

    private func mcuBatterySummary(_ report: MCULabOTAReport, energyJ: Double) -> String {
        let energyText = String(format: "~%.1f J", energyJ)
        if let start = report.mcuBatteryStartMv, let end = report.mcuBatteryEndMv, start > 0, end > 0 {
            let delta = Int(end) - Int(start)
            let sign = delta >= 0 ? "+" : ""
            return "\(energyText) (\(start)→\(end) mV, \(sign)\(delta) mV)"
        }
        if let start = report.mcuBatteryStartMv, start > 0 {
            return "\(energyText) (start \(start) mV)"
        }
        return energyText
    }

    private func phoneBatterySummary(_ report: MCULabOTAReport) -> String? {
        guard let start = report.phoneBatteryStartPct, let end = report.phoneBatteryEndPct else {
            return nil
        }
        let delta = end - start
        let sign = delta >= 0 ? "+" : ""
        return "\(start)% → \(end)% (\(sign)\(delta)%)"
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
            .accessibilityIdentifier("mcuLabOtelAutoForwardToggle")

            Toggle(
                "Authorize with Apple App Attest (mcu-lab-backend Cloud Run)",
                isOn: Binding(
                    get: { controller.useAppAttest },
                    set: { controller.updateUseAppAttest($0) }
                )
            )
            .frame(minHeight: 44)
            .accessibilityIdentifier("mcuLabOtelAppAttestToggle")

            HStack(spacing: 8) {
                TextField(
                    MCULabProtocol.defaultOtelEndpoint,
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
                .accessibilityIdentifier("mcuLabOtelEndpointField")

                Button("POST Now") {
                    controller.forwardLatestSampleNow()
                }
                .buttonStyle(.bordered)
                .disabled(controller.latestSample == nil)
                .frame(minHeight: 44)
                .accessibilityIdentifier("mcuLabOtelPostNowButton")
            }

            HStack {
                Text(controller.lastForwardStatus)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabOtelStatus")
                Spacer()
                Text("Exported: \(controller.forwardedCount)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabOtelExportedCount")
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("mcuLabOtelPanel")
    }

    private var historyPanel: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Recent wake bursts")
                .font(.subheadline.bold())
            if controller.history.isEmpty {
                Text("Deduplicated BLE manufacturer frames appear here.")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("mcuLabHistoryPlaceholder")
            } else {
                ForEach(controller.history) { sample in
                    Text("[\(sample.deviceName)] \(MCULabProtocol.formatStatusLine(sample.metrics)) rssi=\(sample.rssi)")
                        .font(.caption.monospaced())
                        .textSelection(.enabled)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .padding(10)
                        .background(Color.secondary.opacity(0.12), in: RoundedRectangle(cornerRadius: 10))
                }
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
        .accessibilityIdentifier("mcuLabHistoryPanel")
    }

    private var howItWorks: some View {
        VStack(alignment: .leading, spacing: 6) {
            Text("How it works")
                .font(.subheadline.bold())
            Text(
                "Boards running mcu-lab (XIAO ESP32-C3 or Waveshare 7.5″ e-Paper ESP32) record "
                    + "microsecond phase durations and 1 kHz PC hotspots, then broadcast a BLE "
                    + "Manufacturer Specific Data (0xFFFF) packet with their board ID. This bridge "
                    + "listens to all nearby boards simultaneously, forwards each board's metrics "
                    + "and traces separately to GCP (mcu-lab-backend/), and when an OTA update is armed, "
                    + "connects only to the matching board ID, verifies the chip_id and SHA-256, "
                    + "and reboots into the new slot with automatic rollback protection. Firmware "
                    + "lives in mcu-lab/."
            )
            .font(.caption)
            .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private func isOTAInProgress(_ phase: MCULabController.OTAPhase) -> Bool {
        switch phase {
        case .armed, .connecting, .erasing, .streaming, .committing:
            return true
        case .idle, .completed, .failed:
            return false
        }
    }
}

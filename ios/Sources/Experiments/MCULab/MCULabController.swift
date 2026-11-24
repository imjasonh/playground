import Combine
@preconcurrency import CoreBluetooth
import DeviceCheck
import Foundation
#if canImport(UIKit)
import UIKit
#endif

/// A single received BLE telemetry frame from an MCU Lab board.
struct MCULabSample: Identifiable, Equatable {
    let id: UUID
    let deviceId: UUID
    let deviceName: String
    let rssi: Int
    let receivedAt: Date
    let metrics: MCULabMetrics
    var profile: MCULabWakeProfile?
}

/// Scans for MCU Lab BLE Manufacturer Specific Data (`0xFFFF`) bursts,
/// deduplicates frames per device by sequence number (`seq`), updates the live
/// performance and e-paper refresh dashboard, forwards OTLP/HTTP JSON payloads
/// to an OpenTelemetry Collector or the `mcu-lab-backend` Cloud Run service
/// (authorized with Apple App Attest), and installs OTA firmware updates over
/// BLE GATT on the matching board's next wake burst.
@MainActor
final class MCULabController: NSObject, ObservableObject {
    enum OTAPhase: Equatable {
        case idle
        case armed
        case connecting
        case erasing
        case streaming(written: UInt32, total: UInt32)
        case committing
        case completed(sha256: String)
        case failed(String)
    }

    // Preserve legacy UserDefaults / Keychain keys so existing installs keep their
    // registered App Attest key ID and saved collector URL across the rename.
    private static let endpointDefaultsKey = "xiao-esp32c3.otelEndpoint"
    private static let forwardingDefaultsKey = "xiao-esp32c3.forwardingEnabled"
    private static let appAttestEnabledDefaultsKey = "xiao-esp32c3.useAppAttest"
    private static let collectProfileDefaultsKey = "xiao-esp32c3.collectDetailedProfile"
    private static let registeredHostDefaultsKey = "xiao-esp32c3.attestedHost"
    private static let keychainAccount = "xiao-esp32c3.keyId"

    @Published var bluetoothState: CBManagerState = .unknown
    @Published var isScanning = false
    @Published var latestSample: MCULabSample?
    @Published var history: [MCULabSample] = []
    @Published var otelEndpoint: String
    @Published var forwardingEnabled: Bool
    @Published var useAppAttest: Bool
    @Published var collectDetailedProfile: Bool
    @Published var latestTraceId: String?
    @Published var resolvedHotspots: [String: MCULabResolvedSymbol] = [:]
    @Published var forwardedCount = 0
    @Published var lastForwardStatus = "Not forwarded yet."
    @Published var statusMessage = "Flash mcu-lab firmware or inject a simulated wake burst."

    // BLE GATT OTA state
    @Published var selectedBoard: MCULabBoard = .xiaoESP32C3 {
        didSet {
            if !selectedBoard.compatibleApps.contains(selectedApp) {
                selectedApp = selectedBoard.compatibleApps.first ?? .base
            }
        }
    }
    @Published var selectedApp: MCULabApp = .base
    var selectedFirmwareTarget: MCULabFirmwareTarget {
        MCULabFirmwareTarget(board: selectedBoard, app: selectedApp)
    }
    @Published var otaPhase: OTAPhase = .idle
    @Published var stagedFirmwareData: Data?
    @Published var stagedFirmwareName = ""
    @Published var stagedFirmwareSHA256 = ""
    @Published var otaStatusText = "Choose a board and app to pull from GHCR (or pick a .bin) to arm an update."
    @Published var lastOTAReport: MCULabOTAReport?

    private struct OTASessionTracker {
        let deviceId: UUID
        let board: MCULabBoard
        let app: MCULabApp
        let imageName: String
        let sha256: String
        let startedAt: Date
        var beginSentAt: Date?
        var streamStartedAt: Date?
        var commitSentAt: Date?
        var rawBytes: Int = 0
        var wireBytes: Int = 0
        var packetCount: Int = 0
        var chunkSize: Int = 0
        var compression: MCULabOTACompression = .none
        var mcuBatteryStartMv: UInt16?
        var phoneBatteryStartPct: Int?
        var previousBatteryMonitoringEnabled: Bool = false
    }

    private var central: CBCentralManager?
    private var peripherals: [UUID: CBPeripheral] = [:]
    private var otaPeripheral: CBPeripheral?
    private var otaControlChar: CBCharacteristic?
    private var otaDataChar: CBCharacteristic?
    private var otaStatusChar: CBCharacteristic?
    private var otaStreamTask: Task<Void, Never>?
    private var otaWriteAckContinuation: CheckedContinuation<Error?, Never>?
    private var otaWirePayload: Data?
    private var otaWireCompression: MCULabOTACompression = .none
    private var otaSession: OTASessionTracker?
    private var pendingPostOTABatteryDeviceId: UUID?
    private var profilePeripheral: CBPeripheral?
    private var profileTargetDeviceId: UUID?
    private var profileTargetSampleId: UUID?
    private var profileReassembler = MCULabBlobReassembler()
    private var coredumpReassembler = MCULabBlobReassembler()
    private var coredumpChar: CBCharacteristic?

    /// Google Cloud Monitoring rejects custom metric points written more often than once every 5 s per series.
    static let minAutoForwardInterval: TimeInterval = 5.5

    private var lastSeqByDevice: [UUID: UInt8] = [:]
    private var lastAutoForwardByDevice: [UUID: Date] = [:]
    private var simulatedSeq: UInt8 = 0
    private var simulatedWakeCount: UInt32 = 0
    private let defaults: UserDefaults
    private let attestKeys: any AppAttestKeyGenerating
    private let attestStore: any AppAttestStoring
    private let http: any AppAttestHTTPClient
    private let simulatedDeviceId = UUID()

    private let otaServiceUUID = CBUUID(string: MCULabProtocol.otaServiceUUIDString)
    private let otaControlUUID = CBUUID(string: MCULabProtocol.otaControlUUIDString)
    private let otaDataUUID = CBUUID(string: MCULabProtocol.otaDataUUIDString)
    private let otaStatusUUID = CBUUID(string: MCULabProtocol.otaStatusUUIDString)
    private let profileCharUUID = CBUUID(string: MCULabProtocol.profileCharUUIDString)
    private let coredumpCharUUID = CBUUID(string: MCULabProtocol.coredumpCharUUIDString)

    init(
        defaults: UserDefaults = .standard,
        attestKeys: any AppAttestKeyGenerating = SystemAppAttestKeys(),
        attestStore: (any AppAttestStoring)? = nil,
        http: any AppAttestHTTPClient = URLSession.shared
    ) {
        self.defaults = defaults
        self.attestKeys = attestKeys
        self.attestStore = attestStore
            ?? AppAttestUserDefaultsStore(defaults: defaults, keychainAccount: Self.keychainAccount)
        self.http = http
        if let savedEndpoint = defaults.string(forKey: Self.endpointDefaultsKey), !savedEndpoint.isEmpty {
            self.otelEndpoint = savedEndpoint
        } else {
            self.otelEndpoint = MCULabProtocol.defaultOtelEndpoint
        }
        self.forwardingEnabled = defaults.bool(forKey: Self.forwardingDefaultsKey)
        if defaults.object(forKey: Self.appAttestEnabledDefaultsKey) != nil {
            self.useAppAttest = defaults.bool(forKey: Self.appAttestEnabledDefaultsKey)
        } else {
            self.useAppAttest = true
        }
        if defaults.object(forKey: Self.collectProfileDefaultsKey) != nil {
            self.collectDetailedProfile = defaults.bool(forKey: Self.collectProfileDefaultsKey)
        } else {
            self.collectDetailedProfile = true
        }
        super.init()
    }

    var isBluetoothUsable: Bool {
        bluetoothState == .poweredOn
    }

    var availabilitySummary: String {
        switch bluetoothState {
        case .poweredOn:
            return "Bluetooth is on."
        case .poweredOff:
            return "Turn on Bluetooth to scan for MCU Lab advertisements."
        case .unauthorized:
            return "Allow Bluetooth in Settings to scan for MCU Lab boards."
        case .unsupported:
            return "BLE needs a physical iPhone. Use Simulate Wake on the Simulator."
        case .resetting:
            return "Bluetooth is resetting."
        case .unknown:
            return "Waiting for Bluetooth."
        @unknown default:
            return "Bluetooth is unavailable."
        }
    }

    func start() {
        if central == nil {
            central = CBCentralManager(delegate: self, queue: nil)
        }
        applyBluetoothState(central?.state ?? .unknown)
    }

    func stop() {
        otaStreamTask?.cancel()
        central?.stopScan()
        isScanning = false
        peripherals.removeAll()
    }

    func toggleScan() {
        if isScanning {
            stop()
            statusMessage = "Stopped scanning."
        } else {
            startScan()
        }
    }

    func startScan() {
        guard let central, central.state == .poweredOn else {
            statusMessage = availabilitySummary
            return
        }
        isScanning = true
        statusMessage = "Listening for MCU Lab BLE manufacturer bursts (0xFFFF)."
        // Allow duplicates so every new `seq` broadcast is delivered immediately.
        central.scanForPeripherals(
            withServices: nil,
            options: [CBCentralManagerScanOptionAllowDuplicatesKey: true]
        )
    }

    func updateEndpoint(_ value: String) {
        otelEndpoint = value
        defaults.set(value, forKey: Self.endpointDefaultsKey)
    }

    func updateForwardingEnabled(_ enabled: Bool) {
        forwardingEnabled = enabled
        defaults.set(enabled, forKey: Self.forwardingDefaultsKey)
    }

    func updateUseAppAttest(_ enabled: Bool) {
        useAppAttest = enabled
        defaults.set(enabled, forKey: Self.appAttestEnabledDefaultsKey)
    }

    // MARK: - BLE GATT OTA Update

    /// Stage a firmware binary for BLE OTA installation.
    func stageFirmware(data: Data, name: String) {
        guard !data.isEmpty, UInt32(data.count) <= MCULabProtocol.otaSlotBytes else {
            otaPhase = .failed("Firmware size (\(data.count) B) exceeds OTA slot (\(MCULabProtocol.otaSlotBytes) B).")
            otaStatusText = "Firmware size is out of bounds."
            return
        }
        let sha = MCULabProtocol.sha256Hex(data)
        stagedFirmwareData = data
        stagedFirmwareName = name
        stagedFirmwareSHA256 = sha
        otaPhase = .idle
        otaStatusText = "Staged \(name) (\(data.count) B, sha256 \(sha.prefix(12))…)."
    }

    /// Stage a synthetic test firmware binary on Simulator or when testing the OTA flow without GHCR.
    func stageSimulatedFirmware() {
        var fake = Data(repeating: 0x00, count: 24)
        fake[0] = 0xE9 // ESP_IMAGE_HEADER_MAGIC
        let chipID = selectedFirmwareTarget.chipID
        fake[12] = UInt8(truncatingIfNeeded: chipID)
        fake[13] = UInt8(truncatingIfNeeded: chipID >> 8)
        fake.append(Data(repeating: 0xA5, count: 4096))
        stageFirmware(data: fake, name: "\(selectedFirmwareTarget.binName)-sim.bin")
    }

    /// Pull the latest published `mcu-lab` firmware layer from GHCR anonymously.
    /// When `tag` is nil, resolves recent `main` commits touching `mcu-lab` via the GitHub API
    /// and picks the newest 40-char commit SHA with a published GHCR manifest (never uses `:latest`).
    func pullLatestFirmwareFromGHCR(
        target: MCULabFirmwareTarget? = nil,
        tag: String? = nil
    ) async {
        let resolvedTarget = target ?? selectedFirmwareTarget
        let repo = resolvedTarget.ghcrRepo
        guard let tokenURL = URL(string: "https://ghcr.io/token?scope=repository:\(repo):pull") else {
            otaStatusText = "Invalid GHCR repository name."
            return
        }
        do {
            let candidateTags: [String]
            if let explicitTag = tag {
                candidateTags = [explicitTag]
            } else {
                otaStatusText = "Resolving latest \(resolvedTarget.binName) commit on main…"
                candidateTags = try await resolveRecentFirmwareCommitSHAs()
                guard !candidateTags.isEmpty else {
                    otaPhase = .failed("Could not resolve recent mcu-lab commits from GitHub.")
                    otaStatusText = "GitHub commit lookup returned no SHAs."
                    return
                }
            }

            otaStatusText = "Fetching anonymous GHCR token for \(repo)…"
            let (tokData, tokResp) = try await http.data(for: URLRequest(url: tokenURL))
            guard (tokResp as? HTTPURLResponse)?.statusCode == 200,
                  let tokJSON = try JSONSerialization.jsonObject(with: tokData) as? [String: Any],
                  let token = tokJSON["token"] as? String
            else {
                otaPhase = .failed("Could not fetch GHCR anonymous pull token.")
                otaStatusText = "GHCR token fetch failed."
                return
            }

            var resolvedTag: String?
            var resolvedDigest: String?
            for candidate in candidateTags {
                guard let manifestURL = URL(string: "https://ghcr.io/v2/\(repo)/manifests/\(candidate)") else {
                    continue
                }
                var manifestReq = URLRequest(url: manifestURL)
                manifestReq.setValue("Bearer \(token)", forHTTPHeaderField: "Authorization")
                manifestReq.setValue(
                    "application/vnd.oci.image.manifest.v1+json, application/vnd.docker.distribution.manifest.v2+json",
                    forHTTPHeaderField: "Accept"
                )
                let (manData, manResp) = try await http.data(for: manifestReq)
                if (manResp as? HTTPURLResponse)?.statusCode == 200,
                   let manJSON = try JSONSerialization.jsonObject(with: manData) as? [String: Any],
                   let layers = manJSON["layers"] as? [[String: Any]],
                   let firstLayer = layers.first,
                   let digest = firstLayer["digest"] as? String
                {
                    resolvedTag = candidate
                    resolvedDigest = digest
                    break
                }
            }

            guard let chosenTag = resolvedTag, let digest = resolvedDigest else {
                let checked = candidateTags.prefix(3).map { String($0.prefix(7)) }.joined(separator: ", ")
                otaPhase = .failed("No published GHCR image found for \(resolvedTarget.binName) (\(checked)).")
                otaStatusText = "No GHCR layer found for \(resolvedTarget.binName) (\(checked))."
                return
            }

            let shortTag = String(chosenTag.prefix(7))
            otaStatusText = "Downloading \(resolvedTarget.binName)@\(shortTag)…"
            guard let blobURL = URL(string: "https://ghcr.io/v2/\(repo)/blobs/\(digest)") else {
                return
            }
            var blobReq = URLRequest(url: blobURL)
            blobReq.setValue("Bearer \(token)", forHTTPHeaderField: "Authorization")
            let (blobData, blobResp) = try await http.data(for: blobReq)
            guard (blobResp as? HTTPURLResponse)?.statusCode == 200 else {
                otaPhase = .failed("GHCR blob download failed.")
                otaStatusText = "GHCR blob download failed."
                return
            }
            let expectedHex = digest.hasPrefix("sha256:")
                ? String(digest.dropFirst("sha256:".count)).lowercased()
                : digest.lowercased()
            let actualHex = MCULabProtocol.sha256Hex(blobData)
            guard actualHex == expectedHex else {
                otaPhase = .failed("GHCR layer SHA-256 mismatch (got \(actualHex.prefix(12))…, expected \(expectedHex.prefix(12))…).")
                otaStatusText = "GHCR layer digest verification failed."
                return
            }
            if let headerError = MCULabProtocol.validateESPImageHeader(
                blobData,
                expectedChipID: resolvedTarget.chipID
            ) {
                otaPhase = .failed("Chip mismatch for \(resolvedTarget.displayName): \(headerError)")
                otaStatusText = headerError
                return
            }
            stageFirmware(data: blobData, name: "\(resolvedTarget.binName)@\(shortTag) (\(digest.prefix(19)))")
        } catch {
            otaPhase = .failed(error.localizedDescription)
            otaStatusText = "GHCR pull error: \(error.localizedDescription)"
        }
    }

    private func resolveRecentFirmwareCommitSHAs() async throws -> [String] {
        let ghRepo = MCULabProtocol.defaultGitHubRepo
        let workflow = MCULabProtocol.defaultPublishWorkflow

        // Prefer successful `mcu-lab-publish.yml` workflow runs on `main`: CI tags GHCR
        // manifests with `${GITHUB_SHA}` (typically a PR merge commit), whereas GitHub's
        // `commits?path=mcu-lab` API omits merge commits and only returns branch commits.
        if let runsURL = URL(
            string: "https://api.github.com/repos/\(ghRepo)/actions/workflows/\(workflow)/runs?branch=main&status=success&per_page=5"
        ) {
            var req = URLRequest(url: runsURL)
            req.setValue("application/vnd.github+json", forHTTPHeaderField: "Accept")
            if let (data, resp) = try? await http.data(for: req),
               (resp as? HTTPURLResponse)?.statusCode == 200,
               let payload = try? JSONSerialization.jsonObject(with: data) as? [String: Any],
               let runs = payload["workflow_runs"] as? [[String: Any]]
            {
                let shas = Self.deduplicatedValidSHAs(runs.compactMap { $0["head_sha"] as? String })
                if !shas.isEmpty {
                    return shas
                }
            }
        }

        // Fallback: recent commits on `main` without a `path=` filter so merge commits are included.
        guard let url = URL(string: "https://api.github.com/repos/\(ghRepo)/commits?sha=main&per_page=15") else {
            return []
        }
        var req = URLRequest(url: url)
        req.setValue("application/vnd.github+json", forHTTPHeaderField: "Accept")
        let (data, resp) = try await http.data(for: req)
        guard (resp as? HTTPURLResponse)?.statusCode == 200,
              let commits = try JSONSerialization.jsonObject(with: data) as? [[String: Any]]
        else {
            return []
        }
        return Self.deduplicatedValidSHAs(commits.compactMap { $0["sha"] as? String })
    }

    private static func deduplicatedValidSHAs(_ raw: [String]) -> [String] {
        var seen = Set<String>()
        var result: [String] = []
        for entry in raw {
            let sha = entry.lowercased()
            guard sha.count == 40, seen.insert(sha).inserted else {
                continue
            }
            result.append(sha)
        }
        return result
    }

    /// Arm the iPhone to connect on the very next matching board BLE wake burst and stream the staged firmware.
    func armOTAUpdate() {
        guard let data = stagedFirmwareData, !data.isEmpty else {
            otaStatusText = "Stage a firmware image first."
            return
        }
        if let err = MCULabProtocol.validateESPImageHeader(
            data,
            expectedChipID: selectedFirmwareTarget.chipID
        ) {
            otaPhase = .failed(err)
            otaStatusText = "Staged image does not match \(selectedFirmwareTarget.displayName): \(err)"
            return
        }
        otaPhase = .armed
        otaStatusText = "Armed (\(data.count) B). Waiting for the next \(selectedFirmwareTarget.displayName) wake burst to connect…"
        if !isScanning, isBluetoothUsable {
            startScan()
        }
    }

    /// Cancel an armed or in-progress OTA update.
    func cancelOTAUpdate() {
        otaStreamTask?.cancel()
        otaStreamTask = nil
        resumePendingOTAContinuations()
        restorePhoneBatteryMonitoringIfNeeded()
        otaSession = nil
        if let peripheral = otaPeripheral {
            if let ctrl = otaControlChar,
               let abortData = MCULabProtocol.encodeOTACommand(.abort).data(using: .utf8)
            {
                peripheral.writeValue(abortData, for: ctrl, type: .withResponse)
            }
            central?.cancelPeripheralConnection(peripheral)
        }
        otaPeripheral = nil
        otaControlChar = nil
        otaDataChar = nil
        otaStatusChar = nil
        otaPhase = .idle
        otaStatusText = "OTA update cancelled."
    }

    /// Simulate a complete BLE OTA transfer (used when tapping Simulate Wake while OTA is armed).
    private func runSimulatedOTATransfer() {
        guard let data = stagedFirmwareData else {
            return
        }
        let total = UInt32(data.count)
        let sha = stagedFirmwareSHA256
        let compressed = MCULabProtocol.deflateCompress(data)
        let useDeflate = compressed != nil && (compressed?.count ?? data.count) < data.count
        let wireBytes = useDeflate ? (compressed?.count ?? data.count) : data.count
        let packets = max(1, (wireBytes + 469) / 470)
        let streamMs = packets * 30
        let totalMs = 350 + 6_200 + streamMs + 280
        let now = Date()
        let startMv = latestSample?.metrics.batteryMv ?? 3_840
        let report = MCULabOTAReport(
            board: selectedBoard,
            app: selectedApp,
            imageName: stagedFirmwareName,
            sha256: sha,
            compression: useDeflate ? .deflate : .none,
            outcome: "ok",
            rawBytes: data.count,
            wireBytes: wireBytes,
            packetCount: packets,
            chunkSize: 480,
            startedAt: now.addingTimeInterval(-Double(totalMs) / 1_000.0),
            completedAt: now,
            connectMs: 350,
            eraseMs: 6_200,
            streamMs: streamMs,
            commitMs: 280,
            totalMs: totalMs,
            mcuBatteryStartMv: startMv,
            mcuBatteryEndMv: startMv > 25 ? startMv - 22 : startMv,
            phoneBatteryStartPct: readPhoneBatteryPercent(),
            phoneBatteryEndPct: readPhoneBatteryPercent()
        )
        lastOTAReport = report
        otaPhase = .streaming(written: total, total: total)
        otaPhase = .completed(sha256: sha)
        otaStatusText = "Installed \(stagedFirmwareName) (\(total) B, sha256 \(sha.prefix(12))…)."
        if forwardingEnabled {
            forwardOTAReportToOtel(report, deviceId: simulatedDeviceId)
        }
    }

    private func readPhoneBatteryPercent() -> Int? {
        #if canImport(UIKit)
        let level = UIDevice.current.batteryLevel
        guard level >= 0 else { return nil }
        return Int((level * 100.0).rounded())
        #else
        return nil
        #endif
    }

    private func enablePhoneBatteryMonitoring() -> Bool {
        #if canImport(UIKit)
        let prev = UIDevice.current.isBatteryMonitoringEnabled
        UIDevice.current.isBatteryMonitoringEnabled = true
        return prev
        #else
        return false
        #endif
    }

    private func restorePhoneBatteryMonitoringIfNeeded() {
        #if canImport(UIKit)
        if let session = otaSession {
            UIDevice.current.isBatteryMonitoringEnabled = session.previousBatteryMonitoringEnabled
        }
        #endif
    }

    private func finalizeOTASession(outcome: String) {
        guard let session = otaSession else {
            return
        }
        let endPct = readPhoneBatteryPercent()
        restorePhoneBatteryMonitoringIfNeeded()
        otaSession = nil

        let now = Date()
        let beginAt = session.beginSentAt ?? now
        let streamAt = session.streamStartedAt ?? now
        let commitAt = session.commitSentAt ?? now
        let connectMs = max(0, Int((beginAt.timeIntervalSince(session.startedAt) * 1_000.0).rounded()))
        let eraseMs = session.beginSentAt != nil
            ? max(0, Int((streamAt.timeIntervalSince(beginAt) * 1_000.0).rounded()))
            : 0
        let streamMs = session.streamStartedAt != nil
            ? max(0, Int((commitAt.timeIntervalSince(streamAt) * 1_000.0).rounded()))
            : 0
        let commitMs = session.commitSentAt != nil
            ? max(0, Int((now.timeIntervalSince(commitAt) * 1_000.0).rounded()))
            : 0
        let totalMs = max(1, Int((now.timeIntervalSince(session.startedAt) * 1_000.0).rounded()))

        let report = MCULabOTAReport(
            board: session.board,
            app: session.app,
            imageName: session.imageName,
            sha256: session.sha256,
            compression: session.compression,
            outcome: outcome,
            rawBytes: session.rawBytes,
            wireBytes: session.wireBytes,
            packetCount: session.packetCount,
            chunkSize: session.chunkSize,
            startedAt: session.startedAt,
            completedAt: now,
            connectMs: connectMs,
            eraseMs: eraseMs,
            streamMs: streamMs,
            commitMs: commitMs,
            totalMs: totalMs,
            mcuBatteryStartMv: session.mcuBatteryStartMv,
            mcuBatteryEndMv: nil,
            phoneBatteryStartPct: session.phoneBatteryStartPct,
            phoneBatteryEndPct: endPct
        )
        lastOTAReport = report
        if outcome == "ok" {
            pendingPostOTABatteryDeviceId = session.deviceId
        }
        if forwardingEnabled {
            forwardOTAReportToOtel(report, deviceId: session.deviceId)
        }
    }

    private func forwardOTAReportToOtel(_ report: MCULabOTAReport, deviceId: UUID) {
        let trimmed = otelEndpoint.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let metricsURL = Self.resolveMetricsURL(from: trimmed),
              let baseURL = Self.resolveBaseURL(from: metricsURL)
        else {
            return
        }
        let tracesURL = Self.resolveTracesURL(from: baseURL)
        let timeNs = UInt64(report.completedAt.timeIntervalSince1970 * 1_000_000_000)
        let traceId = MCULabProtocol.randomHex(byteCount: 16)
        let rootSpanId = MCULabProtocol.randomHex(byteCount: 8)
        let traceparent = "00-\(traceId)-\(rootSpanId)-01"
        latestTraceId = traceId

        let metricsJSON = MCULabProtocol.formatOTAOTLPMetricsJSON(
            deviceId: deviceId.uuidString,
            report: report,
            timeUnixNano: timeNs
        )
        let traceJSON = MCULabProtocol.formatOTAOTLPTraceJSON(
            traceId: traceId,
            rootSpanId: rootSpanId,
            deviceId: deviceId.uuidString,
            report: report
        )
        guard let metricsBody = metricsJSON.data(using: .utf8),
              let traceBody = traceJSON.data(using: .utf8)
        else {
            return
        }
        let shouldAttest = useAppAttest
        Task { @MainActor in
            do {
                let metricsResult = try await self.postOTLP(
                    body: metricsBody,
                    url: metricsURL,
                    baseURL: baseURL,
                    action: "metrics",
                    authorizeWithAppAttest: shouldAttest,
                    traceparent: traceparent
                )
                let traceResult = try await self.postOTLP(
                    body: traceBody,
                    url: tracesURL,
                    baseURL: baseURL,
                    action: "traces",
                    authorizeWithAppAttest: shouldAttest,
                    traceparent: nil
                )
                if (200..<300).contains(metricsResult.status) {
                    self.forwardedCount += 1
                    self.lastForwardStatus = "Exported OTA report (\(String(format: "%.1f", Double(report.totalMs) / 1000.0)) s, trace \(traceId.prefix(8))…, HTTP \(traceResult.status))."
                }
            } catch {
                self.lastForwardStatus = "OTA report export failed: \(error.localizedDescription)"
            }
        }
    }

    private func resumePendingOTAContinuations() {
        if let ack = otaWriteAckContinuation {
            otaWriteAckContinuation = nil
            ack.resume(returning: nil)
        }
    }

    private func waitForOTAWriteAck() async -> Error? {
        await withCheckedContinuation { (continuation: CheckedContinuation<Error?, Never>) in
            otaWriteAckContinuation?.resume(returning: nil)
            otaWriteAckContinuation = continuation
            Task { @MainActor [weak self] in
                try? await Task.sleep(for: .seconds(5))
                if let pending = self?.otaWriteAckContinuation {
                    self?.otaWriteAckContinuation = nil
                    let timeout = NSError(
                        domain: "MCULabOTA",
                        code: 1,
                        userInfo: [NSLocalizedDescriptionKey: "Timed out waiting for BLE write acknowledgement."]
                    )
                    pending.resume(returning: timeout)
                }
            }
        }
    }

    private func beginOTAConnection(to peripheral: CBPeripheral) {
        guard let central, central.state == .poweredOn else {
            return
        }
        restorePhoneBatteryMonitoringIfNeeded()
        let prevBatteryMon = enablePhoneBatteryMonitoring()
        let preMcuMv = history.first(where: { $0.deviceId == peripheral.identifier })?.metrics.batteryMv
            ?? latestSample?.metrics.batteryMv
        otaSession = OTASessionTracker(
            deviceId: peripheral.identifier,
            board: selectedBoard,
            app: selectedApp,
            imageName: stagedFirmwareName,
            sha256: stagedFirmwareSHA256,
            startedAt: Date(),
            mcuBatteryStartMv: (preMcuMv ?? 0) > 0 ? preMcuMv : nil,
            phoneBatteryStartPct: readPhoneBatteryPercent(),
            previousBatteryMonitoringEnabled: prevBatteryMon
        )
        otaWirePayload = nil
        otaWireCompression = .none
        otaPeripheral = peripheral
        peripheral.delegate = self
        otaPhase = .connecting
        otaStatusText = "Caught wake burst! Connecting to \(peripheral.name ?? MCULabProtocol.deviceName) for OTA…"
        central.connect(peripheral, options: nil)
    }

    private func sendOTABeginIfReady() {
        guard let peripheral = otaPeripheral,
              let ctrl = otaControlChar,
              otaDataChar != nil,
              otaStatusChar != nil,
              let firmware = stagedFirmwareData
        else {
            return
        }
        guard otaPhase == .connecting else {
            return
        }
        otaPhase = .erasing
        if let compressed = MCULabProtocol.deflateCompress(firmware), compressed.count < firmware.count {
            otaWirePayload = compressed
            otaWireCompression = .deflate
        } else {
            otaWirePayload = firmware
            otaWireCompression = .none
        }
        otaSession?.beginSentAt = Date()
        otaSession?.rawBytes = firmware.count
        otaSession?.wireBytes = otaWirePayload?.count ?? firmware.count
        otaSession?.compression = otaWireCompression
        let cmd = MCULabOTACommand.begin(
            size: UInt32(firmware.count),
            sha256: stagedFirmwareSHA256,
            compression: otaWireCompression
        )
        otaStatusText = "Erasing inactive OTA partition for \(firmware.count) bytes…"
        if let encoded = MCULabProtocol.encodeOTACommand(cmd).data(using: .utf8) {
            peripheral.writeValue(encoded, for: ctrl, type: .withResponse)
        }
    }

    private func startStreamingOTAChunks(fromOffset startOffset: UInt32 = 0) {
        guard let peripheral = otaPeripheral,
              let dataChar = otaDataChar,
              let ctrlChar = otaControlChar,
              let firmware = stagedFirmwareData
        else {
            return
        }
        otaStreamTask?.cancel()
        resumePendingOTAContinuations()
        let wirePayload = otaWirePayload ?? firmware
        let mtu = max(peripheral.maximumWriteValueLength(for: .withoutResponse), 180)
        let chunkSize = min(mtu, 480)
        let chunks = MCULabProtocol.chunkFirmwareFramed(
            wirePayload,
            startingAt: startOffset,
            maxPacketBytes: chunkSize
        )
        otaSession?.streamStartedAt = Date()
        otaSession?.packetCount = chunks.count
        otaSession?.chunkSize = chunkSize
        let total = UInt32(firmware.count)
        let wireTotal = UInt32(max(wirePayload.count, 1))
        let initialWritten = otaWireCompression == .deflate
            ? UInt32(Double(startOffset) / Double(wireTotal) * Double(total))
            : startOffset
        otaPhase = .streaming(written: initialWritten, total: total)
        let resumeNote = startOffset > 0 ? " (resuming at \(startOffset) B)" : ""
        if otaWireCompression == .deflate {
            let pctSaved = Int((1.0 - Double(wirePayload.count) / Double(max(firmware.count, 1))) * 100.0)
            otaStatusText = "Streaming \(wirePayload.count) B deflate (\(pctSaved)% smaller than \(total) B)\(resumeNote) in \(chunks.count) ACKed BLE packets…"
        } else {
            otaStatusText = "Streaming \(total) bytes\(resumeNote) in \(chunks.count) ACKed BLE packets (\(chunkSize) B/pkt)…"
        }

        otaStreamTask = Task { @MainActor [weak self] in
            var sentWireBytes: UInt32 = startOffset
            for item in chunks {
                guard let self, !Task.isCancelled else { return }
                // Send every framed chunk with `.withResponse` so BLE ATT provides end-to-end
                // flow control and NimBLE finishes `esp_ota_write` before the next packet arrives.
                peripheral.writeValue(item.frame, for: dataChar, type: .withResponse)
                if let writeError = await self.waitForOTAWriteAck() {
                    if Task.isCancelled { return }
                    self.finalizeOTASession(outcome: "error: \(writeError.localizedDescription)")
                    self.otaPhase = .failed(writeError.localizedDescription)
                    self.otaStatusText = "OTA write failed: \(writeError.localizedDescription)"
                    self.central?.cancelPeripheralConnection(peripheral)
                    return
                }
                sentWireBytes += UInt32(item.payloadCount)
                let progressWritten: UInt32
                if self.otaWireCompression == .deflate {
                    progressWritten = min(total, UInt32(Double(sentWireBytes) / Double(wireTotal) * Double(total)))
                } else {
                    progressWritten = min(total, sentWireBytes)
                }
                self.otaPhase = .streaming(written: progressWritten, total: total)
            }
            guard let self, !Task.isCancelled else { return }
            self.otaSession?.commitSentAt = Date()
            self.otaPhase = .committing
            self.otaStatusText = "Verifying SHA-256 on \(self.selectedFirmwareTarget.displayName) and switching active OTA slot…"
            if let commitData = MCULabProtocol.encodeOTACommand(.commit).data(using: .utf8) {
                peripheral.writeValue(commitData, for: ctrlChar, type: .withResponse)
            }
        }
    }

    func handleOTAStatusNotification(_ line: String) {
        guard let parsed = MCULabProtocol.parseOTAStatus(line) else {
            return
        }
        switch parsed {
        case .idle:
            break
        case .ready(_, let offset):
            if case .streaming = otaPhase {
                // Ignore duplicate READY notifications once ACKed streaming is already active.
                return
            }
            startStreamingOTAChunks(fromOffset: offset)
        case .progress(let written, let total):
            otaPhase = .streaming(written: written, total: total)
            let pct = total > 0 ? Int((Double(written) / Double(total) * 100).rounded()) : 0
            otaStatusText = "Flashing inactive slot: \(written)/\(total) bytes (\(pct)%)."
        case .ok(let sha256):
            otaStreamTask?.cancel()
            resumePendingOTAContinuations()
            finalizeOTASession(outcome: "ok")
            otaPhase = .completed(sha256: sha256)
            otaStatusText = "Update verified (\(sha256.prefix(12))…). \(selectedFirmwareTarget.displayName) is rebooting into the new slot."
            if let peripheral = otaPeripheral {
                central?.cancelPeripheralConnection(peripheral)
            }
        case .error(let message):
            otaStreamTask?.cancel()
            resumePendingOTAContinuations()
            finalizeOTASession(outcome: "error: \(message)")
            otaPhase = .failed(message)
            otaStatusText = "OTA error: \(message)"
            if let peripheral = otaPeripheral {
                central?.cancelPeripheralConnection(peripheral)
            }
        }
    }

    // MARK: - Telemetry & OTLP Forwarding

    /// Inject a realistic wake-cycle telemetry packet for testing on Simulator or without a board nearby.
    func injectSimulatedWake() {
        simulatedSeq = simulatedSeq &+ 1
        simulatedWakeCount += 1

        let isPartial = (simulatedWakeCount % 10) != 0
        var flags: UInt8 = MCULabProtocol.flagDeepSleepWake
            | MCULabProtocol.flagEpdAttached
            | ((selectedFirmwareTarget.boardID & 0x0F) << 4)
        if isPartial {
            flags |= MCULabProtocol.flagEpdPartial
        }

        let metrics = MCULabMetrics(
            seq: simulatedSeq,
            flags: flags,
            wakeCount: simulatedWakeCount,
            sensorUs: 1_380 + UInt32((simulatedWakeCount * 73) % 350),
            computeUs: 3_920 + UInt32((simulatedWakeCount * 131) % 600),
            epdRefreshUs: isPartial ? 320_400 : 1_852_000,
            radioUs: simulatedWakeCount == 1 ? 0 : 150_800,
            batteryMv: UInt16(max(3_300, 4_050 - Int(simulatedWakeCount % 400)))
        )
        let mfg = MCULabProtocol.encodeManufacturerData(metrics)
        let simulatedProfile = collectDetailedProfile
            ? MCULabProtocol.simulatedWakeProfile(for: metrics)
            : nil
        ingestManufacturerData(
            mfg,
            deviceId: simulatedDeviceId,
            deviceName: selectedBoard.gapName,
            rssi: -54,
            profile: simulatedProfile
        )
        if otaPhase == .armed {
            runSimulatedOTATransfer()
        }
    }

    /// Parse a raw `CBAdvertisementDataManufacturerDataKey` buffer, deduplicate by `seq`,
    /// append to history, and optionally forward to the configured OTLP/HTTP endpoint.
    @discardableResult
    func ingestManufacturerData(
        _ mfgData: Data,
        deviceId: UUID,
        deviceName: String,
        rssi: Int,
        now: Date = Date(),
        profile: MCULabWakeProfile? = nil
    ) -> Bool {
        guard let metrics = MCULabProtocol.decodeManufacturerData(mfgData) else {
            return false
        }
        // Capture post-reboot MCU battery voltage from the first wake burst after a completed OTA.
        if pendingPostOTABatteryDeviceId == deviceId, metrics.batteryMv > 0, var report = lastOTAReport {
            pendingPostOTABatteryDeviceId = nil
            report.mcuBatteryEndMv = metrics.batteryMv
            lastOTAReport = report
        }
        // If an OTA update is armed and this advertisement comes from the matching board
        // (`boardID == 0` is legacy XIAO ESP32-C3), connect immediately during its wake window,
        // even if we already saw an earlier advertisement packet from this same burst!
        let advBoardID = metrics.boardID
        let matchesOTATarget = advBoardID == selectedBoard.boardID
            || (advBoardID == 0 && selectedBoard == .xiaoESP32C3)
        if otaPhase == .armed, matchesOTATarget, let peripheral = peripherals[deviceId] {
            beginOTAConnection(to: peripheral)
        }

        // Deduplicate repeated frames from the same advertisement burst before
        // recording history or initiating a GATT profile pull.
        if lastSeqByDevice[deviceId] == metrics.seq {
            return false
        }
        lastSeqByDevice[deviceId] = metrics.seq

        let sample = MCULabSample(
            id: UUID(),
            deviceId: deviceId,
            deviceName: deviceName,
            rssi: rssi,
            receivedAt: now,
            metrics: metrics,
            profile: profile
        )
        latestSample = sample
        history.insert(sample, at: 0)
        if history.count > 25 {
            history = Array(history.prefix(25))
        }
        statusMessage = "Wake #\(metrics.wakeCount) (seq \(metrics.seq)) from \(deviceName) at \(rssi) dBm."

        var initiatedProfilePull = false
        if collectDetailedProfile,
           profile == nil,
           otaPhase == .idle,
           profilePeripheral == nil,
           let peripheral = peripherals[deviceId]
        {
            beginProfileConnection(to: peripheral, deviceId: deviceId, sampleId: sample.id)
            initiatedProfilePull = true
        }

        if forwardingEnabled, !initiatedProfilePull {
            forwardToOtel(sample: sample)
        }
        return true
    }

    func saveCollectDetailedProfile(_ enabled: Bool) {
        collectDetailedProfile = enabled
        defaults.set(enabled, forKey: Self.collectProfileDefaultsKey)
    }

    private func beginProfileConnection(to peripheral: CBPeripheral, deviceId: UUID, sampleId: UUID) {
        guard let central, central.state == .poweredOn else {
            return
        }
        profilePeripheral = peripheral
        profileTargetDeviceId = deviceId
        profileTargetSampleId = sampleId
        peripheral.delegate = self
        central.connect(peripheral, options: nil)
    }

    private func attachWakeProfile(_ profile: MCULabWakeProfile, deviceId: UUID) {
        var updatedSample: MCULabSample?
        if let targetId = profileTargetSampleId,
           let idx = history.firstIndex(where: { $0.id == targetId })
        {
            history[idx].profile = profile
            updatedSample = history[idx]
        } else if let idx = history.firstIndex(where: { $0.deviceId == deviceId && $0.metrics.wakeCount == profile.wakeCount }) {
            history[idx].profile = profile
            updatedSample = history[idx]
        }
        if let updatedSample, latestSample?.id == updatedSample.id {
            latestSample = updatedSample
        } else if var latest = latestSample, updatedSample == nil, latest.deviceId == deviceId {
            latest.profile = profile
            latestSample = latest
            updatedSample = latest
        }
        if forwardingEnabled, let updatedSample {
            forwardToOtel(sample: updatedSample)
        }
    }

    private func finishProfileOnlyConnectionIfNeeded(for peripheral: CBPeripheral, fallbackForward: Bool) {
        guard profilePeripheral?.identifier == peripheral.identifier else {
            return
        }
        let targetDeviceId = profileTargetDeviceId
        let targetSampleId = profileTargetSampleId
        profilePeripheral = nil
        profileTargetDeviceId = nil
        profileTargetSampleId = nil
        if otaPeripheral?.identifier != peripheral.identifier {
            central?.cancelPeripheralConnection(peripheral)
        }
        if fallbackForward, forwardingEnabled {
            if let targetSampleId,
               let sample = history.first(where: { $0.id == targetSampleId && $0.profile == nil })
            {
                forwardToOtel(sample: sample)
            } else if let targetDeviceId,
                      let latest = latestSample,
                      latest.deviceId == targetDeviceId,
                      latest.profile == nil
            {
                forwardToOtel(sample: latest)
            }
        }
    }

    func forwardLatestSampleNow() {
        guard let sample = latestSample else {
            lastForwardStatus = "Receive or simulate a wake packet before forwarding."
            return
        }
        forwardToOtel(sample: sample, isManual: true)
    }

    private func forwardToOtel(sample: MCULabSample, isManual: Bool = false) {
        if !isManual,
           let lastForwarded = lastAutoForwardByDevice[sample.deviceId],
           sample.receivedAt.timeIntervalSince(lastForwarded) < Self.minAutoForwardInterval
        {
            return
        }
        lastAutoForwardByDevice[sample.deviceId] = sample.receivedAt

        let trimmed = otelEndpoint.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let metricsURL = Self.resolveMetricsURL(from: trimmed),
              let baseURL = Self.resolveBaseURL(from: metricsURL)
        else {
            lastForwardStatus = "Invalid OTLP URL: \(trimmed)"
            return
        }
        let tracesURL = Self.resolveTracesURL(from: baseURL)
        let timeNs = UInt64(sample.receivedAt.timeIntervalSince1970 * 1_000_000_000)
        let traceId = MCULabProtocol.randomHex(byteCount: 16)
        let rootSpanId = MCULabProtocol.randomHex(byteCount: 8)
        let traceparent = "00-\(traceId)-\(rootSpanId)-01"
        latestTraceId = traceId

        let metricsJSON = MCULabProtocol.formatOTLPJSON(
            deviceId: sample.deviceId.uuidString,
            metrics: sample.metrics,
            rssi: sample.rssi,
            timeUnixNano: timeNs,
            profile: sample.profile
        )
        let traceJSON = MCULabProtocol.formatOTLPTraceJSON(
            traceId: traceId,
            rootSpanId: rootSpanId,
            deviceId: sample.deviceId.uuidString,
            metrics: sample.metrics,
            rssi: sample.rssi,
            timeUnixNano: timeNs,
            profile: sample.profile
        )
        guard let metricsBody = metricsJSON.data(using: .utf8),
              let traceBody = traceJSON.data(using: .utf8)
        else {
            return
        }

        let wakeNumber = sample.metrics.wakeCount
        let shouldAttest = useAppAttest
        lastForwardStatus = "POSTing wake #\(wakeNumber) metrics + trace to \(metricsURL.host ?? trimmed)…"
        Task { @MainActor in
            do {
                let metricsResult = try await self.postOTLP(
                    body: metricsBody,
                    url: metricsURL,
                    baseURL: baseURL,
                    action: "metrics",
                    authorizeWithAppAttest: shouldAttest,
                    traceparent: traceparent
                )
                guard (200..<300).contains(metricsResult.status) else {
                    let detail = metricsResult.errorMessage.map { " (\($0))" } ?? ""
                    self.lastForwardStatus = "Collector returned HTTP \(metricsResult.status) for wake #\(wakeNumber)\(detail)."
                    return
                }
                let traceResult = try await self.postOTLP(
                    body: traceBody,
                    url: tracesURL,
                    baseURL: baseURL,
                    action: "traces",
                    authorizeWithAppAttest: shouldAttest,
                    traceparent: nil
                )
                self.forwardedCount += 1
                if (200..<300).contains(traceResult.status) {
                    if let body = traceResult.responseBody,
                       let decoded = try? JSONDecoder().decode(TraceIngestResponse.self, from: body),
                       let hotspots = decoded.resolvedHotspots
                    {
                        for (pc, sym) in hotspots {
                            self.resolvedHotspots[pc] = sym
                        }
                    }
                    self.lastForwardStatus = shouldAttest
                        ? "Exported wake #\(wakeNumber) metrics + trace (HTTP \(metricsResult.status), trace \(traceId.prefix(8))…)."
                        : "Exported wake #\(wakeNumber) metrics + trace (HTTP \(metricsResult.status))."
                } else {
                    self.lastForwardStatus = "Exported wake #\(wakeNumber) metrics (HTTP \(metricsResult.status)); trace returned HTTP \(traceResult.status)."
                }
            } catch {
                self.lastForwardStatus = "Export failed: \(error.localizedDescription)"
            }
        }
    }

    /// Export `body` to `metricsURL`, optionally performing the App Attest handshake and
    /// attaching `X-Apple-App-Attest-*` assertion headers for the `mcu-lab-backend` Cloud Run backend.
    func postMetrics(
        body: Data,
        metricsURL: URL,
        baseURL: URL,
        authorizeWithAppAttest: Bool
    ) async throws -> Int {
        let result = try await postOTLP(
            body: body,
            url: metricsURL,
            baseURL: baseURL,
            action: "metrics",
            authorizeWithAppAttest: authorizeWithAppAttest,
            traceparent: nil
        )
        return result.status
    }

    /// Export an OTLP/HTTP v1 JSON trace payload to `tracesURL` with App Attest authorization.
    func postTraces(
        body: Data,
        tracesURL: URL,
        baseURL: URL,
        authorizeWithAppAttest: Bool
    ) async throws -> Int {
        let result = try await postOTLP(
            body: body,
            url: tracesURL,
            baseURL: baseURL,
            action: "traces",
            authorizeWithAppAttest: authorizeWithAppAttest,
            traceparent: nil
        )
        return result.status
    }

    private struct TraceIngestResponse: Decodable {
        var resolvedHotspots: [String: MCULabResolvedSymbol]?
    }

    private struct OTLPPostResult {
        let status: Int
        let errorMessage: String?
        let responseBody: Data?
    }

    private func postOTLP(
        body: Data,
        url: URL,
        baseURL: URL,
        action: String,
        authorizeWithAppAttest: Bool,
        traceparent: String?
    ) async throws -> OTLPPostResult {
        try await postOTLPAttempt(
            body: body,
            url: url,
            baseURL: baseURL,
            action: action,
            authorizeWithAppAttest: authorizeWithAppAttest,
            traceparent: traceparent,
            allowReattestRetry: true
        )
    }

    private func postOTLPAttempt(
        body: Data,
        url: URL,
        baseURL: URL,
        action: String,
        authorizeWithAppAttest: Bool,
        traceparent: String?,
        allowReattestRetry: Bool
    ) async throws -> OTLPPostResult {
        var request = URLRequest(url: url)
        request.httpMethod = "POST"
        request.timeoutInterval = 6
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        if let traceparent {
            request.setValue(traceparent, forHTTPHeaderField: "traceparent")
        }
        request.httpBody = body

        if authorizeWithAppAttest {
            let api = AppAttestAPI(baseURL: baseURL, http: http)
            let keyId = try await ensureBackendAttested(api: api, baseURL: baseURL)
            let challenge = try await api.fetchChallenge()
            let clientData = AppAttestAssertionClientData(
                action: action,
                challenge: challenge.challenge,
                payload: MCULabProtocol.sha256Hex(body)
            )
            let clientJSON = try clientData.jsonBytes()
            request.setValue(keyId, forHTTPHeaderField: "X-Apple-App-Attest-Key-Id")
            request.setValue(
                clientJSON.base64EncodedString(),
                forHTTPHeaderField: "X-Apple-App-Attest-Client-Data"
            )
            if attestKeys.isSupported {
                do {
                    let assertion = try await attestKeys.generateAssertion(
                        keyId,
                        clientDataHash: AppAttestHashing.sha256(clientJSON)
                    )
                    request.setValue(
                        assertion.base64EncodedString(),
                        forHTTPHeaderField: "X-Apple-App-Attest-Assertion"
                    )
                } catch {
                    if Self.shouldRotateAttestKey(error) {
                        clearAttestationState()
                        if allowReattestRetry {
                            return try await postOTLPAttempt(
                                body: body,
                                url: url,
                                baseURL: baseURL,
                                action: action,
                                authorizeWithAppAttest: authorizeWithAppAttest,
                                traceparent: traceparent,
                                allowReattestRetry: false
                            )
                        }
                    }
                    throw error
                }
            }
        }

        let (respData, response) = try await http.data(for: request)
        let code = (response as? HTTPURLResponse)?.statusCode ?? 0
        if code == 401, authorizeWithAppAttest {
            clearAttestationState()
            if allowReattestRetry {
                return try await postOTLPAttempt(
                    body: body,
                    url: url,
                    baseURL: baseURL,
                    action: action,
                    authorizeWithAppAttest: authorizeWithAppAttest,
                    traceparent: traceparent,
                    allowReattestRetry: false
                )
            }
        }
        var errMsg: String?
        if !(200..<300).contains(code),
           let obj = try? JSONSerialization.jsonObject(with: respData) as? [String: Any],
           let msg = obj["error"] as? String
        {
            errMsg = msg
        }
        return OTLPPostResult(status: code, errorMessage: errMsg, responseBody: respData)
    }

    private func clearAttestationState() {
        attestStore.keyId = nil
        attestStore.isRegistered = false
        defaults.removeObject(forKey: Self.registeredHostDefaultsKey)
    }

    private func ensureBackendAttested(api: AppAttestAPI, baseURL: URL) async throws -> String {
        let hostKey = baseURL.absoluteString
        if defaults.string(forKey: Self.registeredHostDefaultsKey) == hostKey,
           let existingKey = attestStore.keyId,
           !existingKey.isEmpty
        {
            return existingKey
        }

        let challenge = try await api.fetchChallenge()
        let userId = attestStore.userId.isEmpty ? "xiao-ios-\(attestStore.deviceId)" : attestStore.userId
        let clientData = AppAttestClientData(
            challenge: challenge.challenge,
            userId: userId,
            deviceId: attestStore.deviceId
        )
        let clientJSON = try clientData.jsonBytes()
        let registered: AppAttestRegisterResponse
        if attestKeys.isSupported {
            let hash = AppAttestHashing.sha256(clientJSON)
            // DCAppAttestService.attestKey is a one-time operation per keyId: calling it on a
            // key that has already been attested throws DCError.invalidInput (error 2). Always
            // generate a fresh Secure Enclave key whenever registering with the backend.
            let keyId = try await attestKeys.generateKey()
            do {
                let attestation = try await attestKeys.attestKey(keyId, clientDataHash: hash)
                registered = try await api.register(
                    keyId: keyId,
                    attestationObject: attestation,
                    clientDataJSON: clientJSON
                )
            } catch {
                if Self.shouldRotateAttestKey(error) {
                    let fresh = try await attestKeys.generateKey()
                    let attestation = try await attestKeys.attestKey(fresh, clientDataHash: hash)
                    registered = try await api.register(
                        keyId: fresh,
                        attestationObject: attestation,
                        clientDataJSON: clientJSON
                    )
                } else {
                    throw error
                }
            }
        } else {
            registered = try await api.registerUnattested(clientDataJSON: clientJSON)
        }
        attestStore.keyId = registered.keyId
        attestStore.isRegistered = true
        defaults.set(hostKey, forKey: Self.registeredHostDefaultsKey)
        return registered.keyId
    }

    private static func shouldRotateAttestKey(_ error: Error) -> Bool {
        let ns = error as NSError
        guard ns.domain == DCError.errorDomain else {
            return false
        }
        return ns.code == DCError.invalidKey.rawValue || ns.code == DCError.invalidInput.rawValue
    }

    static func resolveMetricsURL(from raw: String) -> URL? {
        guard let url = URL(string: raw),
              let scheme = url.scheme,
              scheme == "http" || scheme == "https"
        else {
            return nil
        }
        if url.path.isEmpty || url.path == "/" {
            return url.appending(path: "v1/metrics")
        }
        return url
    }

    static func resolveBaseURL(from metricsURL: URL) -> URL? {
        guard var components = URLComponents(url: metricsURL, resolvingAgainstBaseURL: false) else {
            return nil
        }
        if components.path.hasSuffix("/v1/metrics") {
            let prefix = components.path.dropLast("/v1/metrics".count)
            components.path = prefix.isEmpty ? "/" : String(prefix)
        }
        return components.url
    }

    static func resolveTracesURL(from baseURL: URL) -> URL {
        baseURL.appending(path: "v1/traces")
    }

    static func resolveCoredumpsURL(from baseURL: URL) -> URL {
        baseURL.appending(path: "v1/coredumps")
    }

    private func uploadCoredump(_ elfData: Data, for peripheral: CBPeripheral, characteristic: CBCharacteristic) {
        let trimmed = otelEndpoint.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let metricsURL = Self.resolveMetricsURL(from: trimmed),
              let baseURL = Self.resolveBaseURL(from: metricsURL)
        else {
            return
        }
        let coredumpsURL = Self.resolveCoredumpsURL(from: baseURL)
        let profile = latestSample?.profile
        let payload: [String: Any] = [
            "app": profile?.app ?? selectedFirmwareTarget.binName,
            "board": profile?.board ?? selectedBoard.rawValue,
            "deviceId": peripheral.identifier.uuidString,
            "gitSha": profile?.gitSha ?? "",
            "buildId": profile?.buildId ?? "",
            "elfBase64": elfData.base64EncodedString(),
        ]
        guard let body = try? JSONSerialization.data(withJSONObject: payload) else {
            return
        }
        let shouldAttest = useAppAttest
        Task { @MainActor in
            do {
                let res = try await self.postOTLP(
                    body: body,
                    url: coredumpsURL,
                    baseURL: baseURL,
                    action: "coredump",
                    authorizeWithAppAttest: shouldAttest,
                    traceparent: nil
                )
                if (200..<300).contains(res.status), let clear = "CLEAR".data(using: .utf8) {
                    peripheral.writeValue(clear, for: characteristic, type: .withResponse)
                    self.lastForwardStatus = "Uploaded \(elfData.count) B flash coredump and cleared MCU partition."
                }
            } catch {
                self.lastForwardStatus = "Coredump upload failed: \(error.localizedDescription)"
            }
        }
    }

    private func applyBluetoothState(_ state: CBManagerState) {
        bluetoothState = state
        if state != .poweredOn {
            central?.stopScan()
            isScanning = false
            statusMessage = availabilitySummary
            return
        }
        if !isScanning {
            startScan()
        }
    }
}

extension MCULabController: CBCentralManagerDelegate {
    nonisolated func centralManagerDidUpdateState(_ central: CBCentralManager) {
        let state = central.state
        Task { @MainActor in
            self.applyBluetoothState(state)
        }
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didDiscover peripheral: CBPeripheral,
        advertisementData: [String: Any],
        rssi RSSI: NSNumber
    ) {
        guard let mfg = advertisementData[CBAdvertisementDataManufacturerDataKey] as? Data else {
            return
        }
        let id = peripheral.identifier
        let advertisedName = advertisementData[CBAdvertisementDataLocalNameKey] as? String
        let name = advertisedName ?? peripheral.name ?? MCULabProtocol.deviceName
        let rssi = RSSI.intValue
        Task { @MainActor in
            self.peripherals[id] = peripheral
            self.ingestManufacturerData(mfg, deviceId: id, deviceName: name, rssi: rssi)
        }
    }

    nonisolated func centralManager(_ central: CBCentralManager, didConnect peripheral: CBPeripheral) {
        let service = CBUUID(string: MCULabProtocol.otaServiceUUIDString)
        Task { @MainActor in
            if self.otaPeripheral?.identifier == peripheral.identifier {
                self.otaStatusText = "Connected to \(self.selectedFirmwareTarget.displayName). Discovering OTA service…"
            }
        }
        peripheral.discoverServices([service])
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didFailToConnect peripheral: CBPeripheral,
        error: Error?
    ) {
        let detail = error?.localizedDescription ?? "connection failed"
        Task { @MainActor in
            self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            if self.otaPeripheral?.identifier == peripheral.identifier, self.otaPhase == .connecting {
                // Re-arm for the next wake burst if the wake window closed before connection completed.
                self.restorePhoneBatteryMonitoringIfNeeded()
                self.otaSession = nil
                self.otaPeripheral = nil
                self.otaPhase = .armed
                self.otaStatusText = "Missed wake window (\(detail)); still armed for next wake…"
            }
        }
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didDisconnectPeripheral peripheral: CBPeripheral,
        error: Error?
    ) {
        Task { @MainActor in
            self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            if self.otaPeripheral?.identifier != peripheral.identifier {
                return
            }
            self.otaStreamTask?.cancel()
            self.otaStreamTask = nil
            self.resumePendingOTAContinuations()
            self.otaPeripheral = nil
            self.otaControlChar = nil
            self.otaDataChar = nil
            self.otaStatusChar = nil
            if case .completed = self.otaPhase {
                return
            }
            if case .failed = self.otaPhase {
                return
            }
            if self.otaPhase != .idle && self.otaPhase != .armed {
                self.finalizeOTASession(outcome: "error: BLE link dropped")
                self.otaPhase = .failed("BLE link dropped during OTA transfer.")
                self.otaStatusText = "Disconnected before OTA commit completed."
            }
        }
    }
}

extension MCULabController: CBPeripheralDelegate {
    nonisolated func peripheral(_ peripheral: CBPeripheral, didDiscoverServices error: Error?) {
        if let error {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
                if self.otaPeripheral?.identifier == peripheral.identifier {
                    self.otaPhase = .failed(error.localizedDescription)
                    self.otaStatusText = "OTA service discovery failed: \(error.localizedDescription)"
                }
            }
            return
        }
        let serviceUUID = CBUUID(string: MCULabProtocol.otaServiceUUIDString)
        let ctrlUUID = CBUUID(string: MCULabProtocol.otaControlUUIDString)
        let dataUUID = CBUUID(string: MCULabProtocol.otaDataUUIDString)
        let statusUUID = CBUUID(string: MCULabProtocol.otaStatusUUIDString)
        let profileUUID = CBUUID(string: MCULabProtocol.profileCharUUIDString)
        let coredumpUUID = CBUUID(string: MCULabProtocol.coredumpCharUUIDString)
        guard let services = peripheral.services else {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            }
            return
        }
        var foundService = false
        for service in services where service.uuid == serviceUUID {
            foundService = true
            peripheral.discoverCharacteristics([ctrlUUID, dataUUID, statusUUID, profileUUID, coredumpUUID], for: service)
        }
        if !foundService {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            }
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didDiscoverCharacteristicsFor service: CBService,
        error: Error?
    ) {
        if let error {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
                if self.otaPeripheral?.identifier == peripheral.identifier {
                    self.otaPhase = .failed(error.localizedDescription)
                    self.otaStatusText = "OTA characteristics failed: \(error.localizedDescription)"
                }
            }
            return
        }
        guard let chars = service.characteristics else {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            }
            return
        }
        Task { @MainActor in
            let isProfileOnly = self.profilePeripheral?.identifier == peripheral.identifier
                && self.otaPeripheral?.identifier != peripheral.identifier
            var foundProfileChar = false
            self.profileReassembler.reset()
            self.coredumpReassembler.reset()
            for ch in chars {
                if ch.uuid == self.profileCharUUID, self.collectDetailedProfile {
                    foundProfileChar = true
                    if ch.properties.contains(.notify) {
                        peripheral.setNotifyValue(true, for: ch)
                    } else {
                        peripheral.readValue(for: ch)
                    }
                } else if ch.uuid == self.coredumpCharUUID {
                    self.coredumpChar = ch
                    peripheral.readValue(for: ch)
                }
                if !isProfileOnly {
                    if ch.uuid == self.otaControlUUID {
                        self.otaControlChar = ch
                    } else if ch.uuid == self.otaDataUUID {
                        self.otaDataChar = ch
                    } else if ch.uuid == self.otaStatusUUID {
                        self.otaStatusChar = ch
                        peripheral.setNotifyValue(true, for: ch)
                    }
                }
            }
            if isProfileOnly, !foundProfileChar {
                // Production firmware without profiling enabled does not expose PROFILE_CHAR_UUID.
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            } else if !isProfileOnly {
                self.sendOTABeginIfReady()
            }
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didUpdateValueFor characteristic: CBCharacteristic,
        error: Error?
    ) {
        let statusUUID = CBUUID(string: MCULabProtocol.otaStatusUUIDString)
        let profileUUID = CBUUID(string: MCULabProtocol.profileCharUUIDString)
        let coredumpUUID = CBUUID(string: MCULabProtocol.coredumpCharUUIDString)
        if characteristic.uuid == profileUUID {
            let rawValue = (error == nil) ? characteristic.value : nil
            let deviceId = peripheral.identifier
            Task { @MainActor in
                guard let raw = rawValue else {
                    self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
                    return
                }
                let payload: Data
                if raw.count >= 2 && raw[raw.startIndex] == 0x4D && raw[raw.startIndex + 1] == 0x43 {
                    guard let assembled = self.profileReassembler.push(raw) else {
                        return // Waiting for remaining chunks
                    }
                    payload = assembled
                } else {
                    payload = raw
                }
                if let decoded = MCULabProtocol.decodeWakeProfile(payload) {
                    self.attachWakeProfile(decoded, deviceId: deviceId)
                    self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: false)
                } else {
                    self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
                }
            }
            return
        }
        if characteristic.uuid == coredumpUUID {
            let rawValue = (error == nil) ? characteristic.value : nil
            Task { @MainActor in
                guard let raw = rawValue else { return }
                if let text = String(data: raw, encoding: .utf8), text.trimmingCharacters(in: .whitespacesAndNewlines) == "AVAILABLE" {
                    peripheral.setNotifyValue(true, for: characteristic)
                    return
                }
                if let assembled = self.coredumpReassembler.push(raw) {
                    self.uploadCoredump(assembled, for: peripheral, characteristic: characteristic)
                }
            }
            return
        }
        guard error == nil,
              characteristic.uuid == statusUUID,
              let data = characteristic.value,
              let line = String(data: data, encoding: .utf8)
        else {
            return
        }
        Task { @MainActor in
            self.handleOTAStatusNotification(line)
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didWriteValueFor characteristic: CBCharacteristic,
        error: Error?
    ) {
        let dataUUID = CBUUID(string: MCULabProtocol.otaDataUUIDString)
        guard characteristic.uuid == dataUUID else {
            return
        }
        Task { @MainActor in
            guard self.otaPeripheral?.identifier == peripheral.identifier,
                  let pending = self.otaWriteAckContinuation
            else {
                return
            }
            self.otaWriteAckContinuation = nil
            pending.resume(returning: error)
        }
    }
}

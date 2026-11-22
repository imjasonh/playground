import Combine
@preconcurrency import CoreBluetooth
import DeviceCheck
import Foundation

/// A single received BLE telemetry frame from a Seeed Studio XIAO ESP32C3 board.
struct XIAOESP32C3Sample: Identifiable, Equatable {
    let id: UUID
    let deviceId: UUID
    let deviceName: String
    let rssi: Int
    let receivedAt: Date
    let metrics: XIAOESP32C3Metrics
    var profile: XIAOESP32C3WakeProfile?
}

/// Scans for XIAO ESP32C3 BLE Manufacturer Specific Data (`0xFFFF`) bursts,
/// deduplicates frames by sequence number (`seq`), updates the live performance
/// and e-paper refresh dashboard, forwards OTLP/HTTP JSON payloads to an
/// OpenTelemetry Collector or the `xiao-otel` Cloud Run service (authorized
/// with Apple App Attest), and installs OTA firmware updates over BLE GATT on
/// the board's next wake burst.
@MainActor
final class XIAOESP32C3Controller: NSObject, ObservableObject {
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

    private static let endpointDefaultsKey = "xiao-esp32c3.otelEndpoint"
    private static let forwardingDefaultsKey = "xiao-esp32c3.forwardingEnabled"
    private static let appAttestEnabledDefaultsKey = "xiao-esp32c3.useAppAttest"
    private static let collectProfileDefaultsKey = "xiao-esp32c3.collectDetailedProfile"
    private static let registeredHostDefaultsKey = "xiao-esp32c3.attestedHost"
    private static let keychainAccount = "xiao-esp32c3.keyId"

    @Published var bluetoothState: CBManagerState = .unknown
    @Published var isScanning = false
    @Published var latestSample: XIAOESP32C3Sample?
    @Published var history: [XIAOESP32C3Sample] = []
    @Published var otelEndpoint: String
    @Published var forwardingEnabled: Bool
    @Published var useAppAttest: Bool
    @Published var collectDetailedProfile: Bool
    @Published var latestTraceId: String?
    @Published var resolvedHotspots: [String: XIAOESP32C3ResolvedSymbol] = [:]
    @Published var forwardedCount = 0
    @Published var lastForwardStatus = "Not forwarded yet."
    @Published var statusMessage = "Flash xiao-esp32c3 or inject a simulated wake burst."

    // BLE GATT OTA state
    @Published var selectedFirmwareTarget: MCULabFirmwareTarget = .xiaoESP32C3
    @Published var otaPhase: OTAPhase = .idle
    @Published var stagedFirmwareData: Data?
    @Published var stagedFirmwareName = ""
    @Published var stagedFirmwareSHA256 = ""
    @Published var otaStatusText = "Choose a firmware target and pull from GHCR (or pick a .bin) to arm an update."

    private var central: CBCentralManager?
    private var peripherals: [UUID: CBPeripheral] = [:]
    private var otaPeripheral: CBPeripheral?
    private var otaControlChar: CBCharacteristic?
    private var otaDataChar: CBCharacteristic?
    private var otaStatusChar: CBCharacteristic?
    private var otaStreamTask: Task<Void, Never>?
    private var profilePeripheral: CBPeripheral?
    private var profileTargetDeviceId: UUID?

    private var lastSeqByDevice: [UUID: UInt8] = [:]
    private var simulatedSeq: UInt8 = 0
    private var simulatedWakeCount: UInt32 = 0
    private let defaults: UserDefaults
    private let attestKeys: any AppAttestKeyGenerating
    private let attestStore: any AppAttestStoring
    private let http: any AppAttestHTTPClient
    private let simulatedDeviceId = UUID()

    private let otaServiceUUID = CBUUID(string: XIAOESP32C3Protocol.otaServiceUUIDString)
    private let otaControlUUID = CBUUID(string: XIAOESP32C3Protocol.otaControlUUIDString)
    private let otaDataUUID = CBUUID(string: XIAOESP32C3Protocol.otaDataUUIDString)
    private let otaStatusUUID = CBUUID(string: XIAOESP32C3Protocol.otaStatusUUIDString)
    private let profileCharUUID = CBUUID(string: XIAOESP32C3Protocol.profileCharUUIDString)

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
            self.otelEndpoint = XIAOESP32C3Protocol.defaultOtelEndpoint
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
            return "Turn on Bluetooth to scan for XIAO-C3 advertisements."
        case .unauthorized:
            return "Allow Bluetooth in Settings to scan for XIAO-C3."
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
        statusMessage = "Listening for XIAO-C3 BLE manufacturer bursts (0xFFFF)."
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
        guard !data.isEmpty, UInt32(data.count) <= XIAOESP32C3Protocol.otaSlotBytes else {
            otaPhase = .failed("Firmware size (\(data.count) B) exceeds OTA slot (\(XIAOESP32C3Protocol.otaSlotBytes) B).")
            otaStatusText = "Firmware size is out of bounds."
            return
        }
        let sha = XIAOESP32C3Protocol.sha256Hex(data)
        stagedFirmwareData = data
        stagedFirmwareName = name
        stagedFirmwareSHA256 = sha
        otaPhase = .idle
        otaStatusText = "Staged \(name) (\(data.count) B, sha256 \(sha.prefix(12))…)."
    }

    /// Stage a synthetic test firmware binary on Simulator or when testing the OTA flow without GHCR.
    func stageSimulatedFirmware() {
        var fake = Data("ESP-IDF-XIAO-ESP32C3-OTA-TEST-".utf8)
        fake.append(Data(repeating: 0xA5, count: 4096))
        stageFirmware(data: fake, name: "xiao-esp32c3-sim.bin")
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
                otaStatusText = "Resolving latest \(resolvedTarget.rawValue) commit on main…"
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
                otaPhase = .failed("No published GHCR image found for \(resolvedTarget.rawValue) (\(checked)).")
                otaStatusText = "No GHCR layer found for \(resolvedTarget.rawValue) (\(checked))."
                return
            }

            let shortTag = String(chosenTag.prefix(7))
            otaStatusText = "Downloading \(resolvedTarget.rawValue)@\(shortTag)…"
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
            let actualHex = XIAOESP32C3Protocol.sha256Hex(blobData)
            guard actualHex == expectedHex else {
                otaPhase = .failed("GHCR layer SHA-256 mismatch (got \(actualHex.prefix(12))…, expected \(expectedHex.prefix(12))…).")
                otaStatusText = "GHCR layer digest verification failed."
                return
            }
            if let headerError = XIAOESP32C3Protocol.validateESPImageHeader(
                blobData,
                expectedChipID: resolvedTarget.chipID
            ) {
                otaPhase = .failed("Chip mismatch for \(resolvedTarget.displayName): \(headerError)")
                otaStatusText = headerError
                return
            }
            stageFirmware(data: blobData, name: "\(resolvedTarget.rawValue)@\(shortTag) (\(digest.prefix(19)))")
        } catch {
            otaPhase = .failed(error.localizedDescription)
            otaStatusText = "GHCR pull error: \(error.localizedDescription)"
        }
    }

    private func resolveRecentFirmwareCommitSHAs() async throws -> [String] {
        let ghRepo = XIAOESP32C3Protocol.defaultGitHubRepo
        let fwPath = XIAOESP32C3Protocol.defaultFirmwarePath
        guard let url = URL(string: "https://api.github.com/repos/\(ghRepo)/commits?sha=main&path=\(fwPath)&per_page=5") else {
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
        return commits.compactMap { entry -> String? in
            guard let sha = entry["sha"] as? String, sha.count == 40 else {
                return nil
            }
            return sha.lowercased()
        }
    }

    /// Arm the iPhone to connect on the very next XIAO BLE wake burst and stream the staged firmware.
    func armOTAUpdate() {
        guard let data = stagedFirmwareData, !data.isEmpty else {
            otaStatusText = "Stage a firmware image first."
            return
        }
        otaPhase = .armed
        otaStatusText = "Armed (\(data.count) B). Waiting for the next XIAO-C3 wake burst to connect…"
        if !isScanning, isBluetoothUsable {
            startScan()
        }
    }

    /// Cancel an armed or in-progress OTA update.
    func cancelOTAUpdate() {
        otaStreamTask?.cancel()
        otaStreamTask = nil
        if let peripheral = otaPeripheral, let ctrl = otaControlChar {
            if let abortData = XIAOESP32C3Protocol.encodeOTACommand(.abort).data(using: .utf8) {
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
        otaPhase = .streaming(written: total, total: total)
        otaPhase = .completed(sha256: sha)
        otaStatusText = "Installed \(stagedFirmwareName) (\(total) B, sha256 \(sha.prefix(12))…)."
    }

    private func beginOTAConnection(to peripheral: CBPeripheral) {
        guard let central, central.state == .poweredOn else {
            return
        }
        otaPeripheral = peripheral
        peripheral.delegate = self
        otaPhase = .connecting
        otaStatusText = "Caught wake burst! Connecting to \(peripheral.name ?? XIAOESP32C3Protocol.deviceName) for OTA…"
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
        let cmd = XIAOESP32C3OTACommand.begin(
            size: UInt32(firmware.count),
            sha256: stagedFirmwareSHA256
        )
        otaStatusText = "Erasing inactive OTA partition for \(firmware.count) bytes…"
        if let encoded = XIAOESP32C3Protocol.encodeOTACommand(cmd).data(using: .utf8) {
            peripheral.writeValue(encoded, for: ctrl, type: .withResponse)
        }
    }

    private func startStreamingOTAChunks() {
        guard let peripheral = otaPeripheral,
              let dataChar = otaDataChar,
              let ctrlChar = otaControlChar,
              let firmware = stagedFirmwareData
        else {
            return
        }
        otaStreamTask?.cancel()
        let mtu = max(peripheral.maximumWriteValueLength(for: .withoutResponse), 180)
        let chunkSize = min(mtu, 480)
        let chunks = XIAOESP32C3Protocol.chunkFirmware(firmware, chunkSize: chunkSize)
        let total = UInt32(firmware.count)
        otaPhase = .streaming(written: 0, total: total)
        otaStatusText = "Streaming \(total) bytes in \(chunks.count) BLE packets (\(chunkSize) B/pkt)…"

        otaStreamTask = Task { @MainActor [weak self] in
            var sentBytes: UInt32 = 0
            for (idx, chunk) in chunks.enumerated() {
                if Task.isCancelled { return }
                peripheral.writeValue(chunk, for: dataChar, type: .withoutResponse)
                sentBytes += UInt32(chunk.count)
                if idx % 16 == 0 || sentBytes == total {
                    self?.otaPhase = .streaming(written: sentBytes, total: total)
                    try? await Task.sleep(for: .milliseconds(12))
                } else {
                    try? await Task.sleep(for: .milliseconds(3))
                }
            }
            guard let self, !Task.isCancelled else { return }
            self.otaPhase = .committing
            self.otaStatusText = "Verifying SHA-256 on XIAO and switching active OTA slot…"
            if let commitData = XIAOESP32C3Protocol.encodeOTACommand(.commit).data(using: .utf8) {
                peripheral.writeValue(commitData, for: ctrlChar, type: .withResponse)
            }
        }
    }

    func handleOTAStatusNotification(_ line: String) {
        guard let parsed = XIAOESP32C3Protocol.parseOTAStatus(line) else {
            return
        }
        switch parsed {
        case .idle:
            break
        case .ready:
            startStreamingOTAChunks()
        case .progress(let written, let total):
            otaPhase = .streaming(written: written, total: total)
            let pct = total > 0 ? Int((Double(written) / Double(total) * 100).rounded()) : 0
            otaStatusText = "Flashing inactive slot: \(written)/\(total) bytes (\(pct)%)."
        case .ok(let sha256):
            otaStreamTask?.cancel()
            otaPhase = .completed(sha256: sha256)
            otaStatusText = "Update verified (\(sha256.prefix(12))…). XIAO-C3 is rebooting into the new slot."
            if let peripheral = otaPeripheral {
                central?.cancelPeripheralConnection(peripheral)
            }
        case .error(let message):
            otaStreamTask?.cancel()
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
        var flags: UInt8 = XIAOESP32C3Protocol.flagDeepSleepWake | XIAOESP32C3Protocol.flagEpdAttached
        if isPartial {
            flags |= XIAOESP32C3Protocol.flagEpdPartial
        }

        let metrics = XIAOESP32C3Metrics(
            seq: simulatedSeq,
            flags: flags,
            wakeCount: simulatedWakeCount,
            sensorUs: 1_380 + UInt32((simulatedWakeCount * 73) % 350),
            computeUs: 3_920 + UInt32((simulatedWakeCount * 131) % 600),
            epdRefreshUs: isPartial ? 320_400 : 1_852_000,
            radioUs: simulatedWakeCount == 1 ? 0 : 150_800,
            batteryMv: UInt16(max(3_300, 4_050 - Int(simulatedWakeCount % 400)))
        )
        let mfg = XIAOESP32C3Protocol.encodeManufacturerData(metrics)
        let simulatedProfile = collectDetailedProfile
            ? XIAOESP32C3Protocol.simulatedWakeProfile(for: metrics)
            : nil
        ingestManufacturerData(
            mfg,
            deviceId: simulatedDeviceId,
            deviceName: XIAOESP32C3Protocol.deviceName,
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
        profile: XIAOESP32C3WakeProfile? = nil
    ) -> Bool {
        guard let metrics = XIAOESP32C3Protocol.decodeManufacturerData(mfgData) else {
            return false
        }
        // If an OTA update is armed and this advertisement comes from the matching board
        // (`boardID == 0` is legacy XIAO ESP32-C3), connect immediately during its wake window!
        let advBoardID = (metrics.flags >> 4) & 0x0F
        let matchesOTATarget = advBoardID == selectedFirmwareTarget.boardID
            || (advBoardID == 0 && selectedFirmwareTarget == .xiaoESP32C3)
        var initiatedProfilePull = false
        if otaPhase == .armed, matchesOTATarget, let peripheral = peripherals[deviceId] {
            beginOTAConnection(to: peripheral)
        } else if collectDetailedProfile,
                  profile == nil,
                  otaPhase == .idle,
                  profilePeripheral == nil,
                  let peripheral = peripherals[deviceId]
        {
            beginProfileConnection(to: peripheral, deviceId: deviceId)
            initiatedProfilePull = true
        }

        // Deduplicate repeated frames from the same 150 ms burst.
        if lastSeqByDevice[deviceId] == metrics.seq {
            return false
        }
        lastSeqByDevice[deviceId] = metrics.seq

        let sample = XIAOESP32C3Sample(
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

        if forwardingEnabled, !initiatedProfilePull {
            forwardToOtel(sample: sample)
        }
        return true
    }

    func saveCollectDetailedProfile(_ enabled: Bool) {
        collectDetailedProfile = enabled
        defaults.set(enabled, forKey: Self.collectProfileDefaultsKey)
    }

    private func beginProfileConnection(to peripheral: CBPeripheral, deviceId: UUID) {
        guard let central, central.state == .poweredOn else {
            return
        }
        profilePeripheral = peripheral
        profileTargetDeviceId = deviceId
        peripheral.delegate = self
        central.connect(peripheral, options: nil)
    }

    private func attachWakeProfile(_ profile: XIAOESP32C3WakeProfile, deviceId: UUID) {
        var updatedSample: XIAOESP32C3Sample?
        if var latest = latestSample, latest.deviceId == deviceId {
            latest.profile = profile
            latestSample = latest
            updatedSample = latest
        }
        if let idx = history.firstIndex(where: { $0.deviceId == deviceId && $0.metrics.wakeCount == profile.wakeCount }) {
            history[idx].profile = profile
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
        profilePeripheral = nil
        profileTargetDeviceId = nil
        if otaPeripheral?.identifier != peripheral.identifier {
            central?.cancelPeripheralConnection(peripheral)
        }
        if fallbackForward,
           forwardingEnabled,
           let targetDeviceId,
           let latest = latestSample,
           latest.deviceId == targetDeviceId,
           latest.profile == nil
        {
            forwardToOtel(sample: latest)
        }
    }

    func forwardLatestSampleNow() {
        guard let sample = latestSample else {
            lastForwardStatus = "Receive or simulate a wake packet before forwarding."
            return
        }
        forwardToOtel(sample: sample)
    }

    private func forwardToOtel(sample: XIAOESP32C3Sample) {
        let trimmed = otelEndpoint.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let metricsURL = Self.resolveMetricsURL(from: trimmed),
              let baseURL = Self.resolveBaseURL(from: metricsURL)
        else {
            lastForwardStatus = "Invalid OTLP URL: \(trimmed)"
            return
        }
        let tracesURL = Self.resolveTracesURL(from: baseURL)
        let timeNs = UInt64(sample.receivedAt.timeIntervalSince1970 * 1_000_000_000)
        let traceId = XIAOESP32C3Protocol.randomHex(byteCount: 16)
        let rootSpanId = XIAOESP32C3Protocol.randomHex(byteCount: 8)
        let traceparent = "00-\(traceId)-\(rootSpanId)-01"
        latestTraceId = traceId

        let metricsJSON = XIAOESP32C3Protocol.formatOTLPJSON(
            deviceId: sample.deviceId.uuidString,
            metrics: sample.metrics,
            rssi: sample.rssi,
            timeUnixNano: timeNs,
            profile: sample.profile
        )
        let traceJSON = XIAOESP32C3Protocol.formatOTLPTraceJSON(
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
    /// attaching `X-Apple-App-Attest-*` assertion headers for the `xiao-otel` Cloud Run backend.
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
        var resolvedHotspots: [String: XIAOESP32C3ResolvedSymbol]?
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
                payload: XIAOESP32C3Protocol.sha256Hex(body)
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

extension XIAOESP32C3Controller: CBCentralManagerDelegate {
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
        let name = advertisedName ?? peripheral.name ?? XIAOESP32C3Protocol.deviceName
        let rssi = RSSI.intValue
        Task { @MainActor in
            self.peripherals[id] = peripheral
            self.ingestManufacturerData(mfg, deviceId: id, deviceName: name, rssi: rssi)
        }
    }

    nonisolated func centralManager(_ central: CBCentralManager, didConnect peripheral: CBPeripheral) {
        let service = CBUUID(string: XIAOESP32C3Protocol.otaServiceUUIDString)
        Task { @MainActor in
            if self.otaPeripheral?.identifier == peripheral.identifier {
                self.otaStatusText = "Connected to XIAO-C3. Discovering OTA service…"
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
            if self.otaPhase == .connecting {
                // Re-arm for the next wake burst if the 150 ms window closed before connection completed.
                self.otaPhase = .armed
                self.otaStatusText = "Missed 150 ms wake window (\(detail)); still armed for next wake…"
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
                self.otaPhase = .failed("BLE link dropped during OTA transfer.")
                self.otaStatusText = "Disconnected before OTA commit completed."
            }
        }
    }
}

extension XIAOESP32C3Controller: CBPeripheralDelegate {
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
        let serviceUUID = CBUUID(string: XIAOESP32C3Protocol.otaServiceUUIDString)
        let ctrlUUID = CBUUID(string: XIAOESP32C3Protocol.otaControlUUIDString)
        let dataUUID = CBUUID(string: XIAOESP32C3Protocol.otaDataUUIDString)
        let statusUUID = CBUUID(string: XIAOESP32C3Protocol.otaStatusUUIDString)
        let profileUUID = CBUUID(string: XIAOESP32C3Protocol.profileCharUUIDString)
        guard let services = peripheral.services else {
            Task { @MainActor in
                self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
            }
            return
        }
        var foundService = false
        for service in services where service.uuid == serviceUUID {
            foundService = true
            peripheral.discoverCharacteristics([ctrlUUID, dataUUID, statusUUID, profileUUID], for: service)
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
            for ch in chars {
                if ch.uuid == self.profileCharUUID, self.collectDetailedProfile {
                    foundProfileChar = true
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
        let statusUUID = CBUUID(string: XIAOESP32C3Protocol.otaStatusUUIDString)
        let profileUUID = CBUUID(string: XIAOESP32C3Protocol.profileCharUUIDString)
        if characteristic.uuid == profileUUID {
            let decoded = (error == nil) ? characteristic.value.flatMap(XIAOESP32C3Protocol.decodeWakeProfile) : nil
            let deviceId = peripheral.identifier
            Task { @MainActor in
                if let decoded {
                    self.attachWakeProfile(decoded, deviceId: deviceId)
                    self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: false)
                } else {
                    self.finishProfileOnlyConnectionIfNeeded(for: peripheral, fallbackForward: true)
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
}

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
}

/// Scans for connectionless XIAO ESP32C3 BLE Manufacturer Specific Data (`0xFFFF`)
/// bursts, deduplicates frames by sequence number (`seq`), updates the live
/// performance and e-paper refresh dashboard, and optionally POSTs OTLP/HTTP
/// JSON payloads to an OpenTelemetry Collector or the `xiao-otel` Cloud Run
/// service (authorized with Apple App Attest).
@MainActor
final class XIAOESP32C3Controller: NSObject, ObservableObject {
    private static let endpointDefaultsKey = "xiao-esp32c3.otelEndpoint"
    private static let forwardingDefaultsKey = "xiao-esp32c3.forwardingEnabled"
    private static let appAttestEnabledDefaultsKey = "xiao-esp32c3.useAppAttest"
    private static let registeredHostDefaultsKey = "xiao-esp32c3.attestedHost"

    @Published var bluetoothState: CBManagerState = .unknown
    @Published var isScanning = false
    @Published var latestSample: XIAOESP32C3Sample?
    @Published var history: [XIAOESP32C3Sample] = []
    @Published var otelEndpoint: String
    @Published var forwardingEnabled: Bool
    @Published var useAppAttest: Bool
    @Published var forwardedCount = 0
    @Published var lastForwardStatus = "Not forwarded yet."
    @Published var statusMessage = "Flash xiao-esp32c3 or inject a simulated wake burst."

    private var central: CBCentralManager?
    private var lastSeqByDevice: [UUID: UInt8] = [:]
    private var simulatedSeq: UInt8 = 0
    private var simulatedWakeCount: UInt32 = 0
    private let defaults: UserDefaults
    private let attestKeys: any AppAttestKeyGenerating
    private let attestStore: any AppAttestStoring
    private let http: any AppAttestHTTPClient
    private let simulatedDeviceId = UUID()

    init(
        defaults: UserDefaults = .standard,
        attestKeys: any AppAttestKeyGenerating = SystemAppAttestKeys(),
        attestStore: (any AppAttestStoring)? = nil,
        http: any AppAttestHTTPClient = URLSession.shared
    ) {
        self.defaults = defaults
        self.attestKeys = attestKeys
        self.attestStore = attestStore ?? AppAttestUserDefaultsStore(defaults: defaults)
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
        central?.stopScan()
        isScanning = false
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
        ingestManufacturerData(
            mfg,
            deviceId: simulatedDeviceId,
            deviceName: XIAOESP32C3Protocol.deviceName,
            rssi: -54
        )
    }

    /// Parse a raw `CBAdvertisementDataManufacturerDataKey` buffer, deduplicate by `seq`,
    /// append to history, and optionally forward to the configured OTLP/HTTP endpoint.
    @discardableResult
    func ingestManufacturerData(
        _ mfgData: Data,
        deviceId: UUID,
        deviceName: String,
        rssi: Int,
        now: Date = Date()
    ) -> Bool {
        guard let metrics = XIAOESP32C3Protocol.decodeManufacturerData(mfgData) else {
            return false
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
            metrics: metrics
        )
        latestSample = sample
        history.insert(sample, at: 0)
        if history.count > 25 {
            history = Array(history.prefix(25))
        }
        statusMessage = "Wake #\(metrics.wakeCount) (seq \(metrics.seq)) from \(deviceName) at \(rssi) dBm."

        if forwardingEnabled {
            forwardToOtel(sample: sample)
        }
        return true
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
        let timeNs = UInt64(sample.receivedAt.timeIntervalSince1970 * 1_000_000_000)
        let json = XIAOESP32C3Protocol.formatOTLPJSON(
            deviceId: sample.deviceId.uuidString,
            metrics: sample.metrics,
            rssi: sample.rssi,
            timeUnixNano: timeNs
        )
        guard let body = json.data(using: .utf8) else {
            return
        }

        let wakeNumber = sample.metrics.wakeCount
        let shouldAttest = useAppAttest
        lastForwardStatus = "POSTing wake #\(wakeNumber) to \(metricsURL.host ?? trimmed)…"
        Task { @MainActor in
            do {
                let code = try await self.postMetrics(
                    body: body,
                    metricsURL: metricsURL,
                    baseURL: baseURL,
                    authorizeWithAppAttest: shouldAttest
                )
                if (200..<300).contains(code) {
                    self.forwardedCount += 1
                    self.lastForwardStatus = shouldAttest
                        ? "Exported wake #\(wakeNumber) with App Attest (HTTP \(code))."
                        : "Exported wake #\(wakeNumber) (HTTP \(code))."
                } else {
                    self.lastForwardStatus = "Collector returned HTTP \(code) for wake #\(wakeNumber)."
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
        var request = URLRequest(url: metricsURL)
        request.httpMethod = "POST"
        request.timeoutInterval = 6
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        request.httpBody = body

        if authorizeWithAppAttest {
            let api = AppAttestAPI(baseURL: baseURL, http: http)
            let keyId = try await ensureBackendAttested(api: api, baseURL: baseURL)
            let challenge = try await api.fetchChallenge()
            let clientData = AppAttestAssertionClientData(
                action: "metrics",
                challenge: challenge.challenge
            )
            let clientJSON = try clientData.jsonBytes()
            request.setValue(keyId, forHTTPHeaderField: "X-Apple-App-Attest-Key-Id")
            request.setValue(
                clientJSON.base64EncodedString(),
                forHTTPHeaderField: "X-Apple-App-Attest-Client-Data"
            )
            if attestKeys.isSupported {
                let assertion = try await attestKeys.generateAssertion(
                    keyId,
                    clientDataHash: AppAttestHashing.sha256(clientJSON)
                )
                request.setValue(
                    assertion.base64EncodedString(),
                    forHTTPHeaderField: "X-Apple-App-Attest-Assertion"
                )
            }
        }

        let (_, response) = try await http.data(for: request)
        let code = (response as? HTTPURLResponse)?.statusCode ?? 0
        if code == 401, authorizeWithAppAttest {
            // If Cloud Run restarted and lost in-memory registration, re-register once and retry.
            defaults.removeObject(forKey: Self.registeredHostDefaultsKey)
        }
        return code
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
            let keyId: String
            if let existing = attestStore.keyId, !existing.isEmpty {
                keyId = existing
            } else {
                let fresh = try await attestKeys.generateKey()
                attestStore.keyId = fresh
                keyId = fresh
            }
            let attestation = try await attestKeys.attestKey(keyId, clientDataHash: hash)
            registered = try await api.register(
                keyId: keyId,
                attestationObject: attestation,
                clientDataJSON: clientJSON
            )
        } else {
            registered = try await api.registerUnattested(clientDataJSON: clientJSON)
        }
        attestStore.keyId = registered.keyId
        attestStore.isRegistered = true
        defaults.set(hostKey, forKey: Self.registeredHostDefaultsKey)
        return registered.keyId
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
            self.ingestManufacturerData(mfg, deviceId: id, deviceName: name, rssi: rssi)
        }
    }
}

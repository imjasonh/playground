import DeviceCheck
import XCTest
@testable import Playground

final class XIAOESP32C3ProtocolTests: XCTestCase {
    func testManufacturerDataRoundTrip() {
        let metrics = XIAOESP32C3Metrics(
            seq: 42,
            flags: XIAOESP32C3Protocol.flagDeepSleepWake | XIAOESP32C3Protocol.flagEpdPartial,
            wakeCount: 1_024,
            sensorUs: 1_450,
            computeUs: 3_820,
            epdRefreshUs: 320_500,
            radioUs: 152_000,
            batteryMv: 3_910
        )
        let mfg = XIAOESP32C3Protocol.encodeManufacturerData(metrics)
        XCTAssertEqual(mfg.count, XIAOESP32C3Protocol.manufacturerDataLength)
        XCTAssertEqual(mfg[0], 0xFF)
        XCTAssertEqual(mfg[1], 0xFF)

        let decoded = XIAOESP32C3Protocol.decodeManufacturerData(mfg)
        XCTAssertEqual(decoded, metrics)
        XCTAssertEqual(decoded?.isDeepSleepWake, true)
        XCTAssertEqual(decoded?.isEpdPartialRefresh, true)
        XCTAssertEqual(decoded?.isEpdAttached, false)
        XCTAssertEqual(decoded?.isBrownoutReset, false)
        XCTAssertEqual(decoded?.totalActiveUs, 477_770)
    }

    func testDecodeRejectsWrongCompanyIDAndShortBuffers() {
        let metrics = XIAOESP32C3Metrics(
            seq: 1,
            flags: 0,
            wakeCount: 1,
            sensorUs: 900,
            computeUs: 2_100,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 4_000
        )
        var mfg = XIAOESP32C3Protocol.encodeManufacturerData(metrics)
        mfg[0] = 0x4C
        mfg[1] = 0x00
        XCTAssertNil(XIAOESP32C3Protocol.decodeManufacturerData(mfg))
        XCTAssertNil(XIAOESP32C3Protocol.decodeManufacturerData(Data([0xFF, 0xFF, 0x01])))
    }

    func testFormatStatusLineMatchesFirmware() {
        let metrics = XIAOESP32C3Metrics(
            seq: 12,
            flags: XIAOESP32C3Protocol.flagDeepSleepWake | XIAOESP32C3Protocol.flagEpdPartial,
            wakeCount: 12,
            sensorUs: 1_340,
            computeUs: 4_120,
            epdRefreshUs: 320_000,
            radioUs: 149_500,
            batteryMv: 3_880
        )
        XCTAssertEqual(
            XIAOESP32C3Protocol.formatStatusLine(metrics),
            "seq=12 wake=12 sensor_us=1340 compute_us=4120 epd_us=320000 radio_us=149500 batt_mv=3880 flags=0x05"
        )
    }

    func testFormatOTLPJSONContainsAllMetricsAndPhases() throws {
        let metrics = XIAOESP32C3Metrics(
            seq: 3,
            flags: XIAOESP32C3Protocol.flagDeepSleepWake,
            wakeCount: 15,
            sensorUs: 1_100,
            computeUs: 3_400,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 3_890
        )
        let jsonString = XIAOESP32C3Protocol.formatOTLPJSON(
            deviceId: "xiao-c3-01",
            metrics: metrics,
            rssi: -58,
            timeUnixNano: 1_700_000_000_000_000_000
        )
        let data = try XCTUnwrap(jsonString.data(using: .utf8))
        let parsed = try XCTUnwrap(JSONSerialization.jsonObject(with: data) as? [String: Any])
        XCTAssertNotNil(parsed["resourceMetrics"])
        XCTAssertTrue(jsonString.contains(#""service.name","value":{"stringValue":"xiao-esp32c3"}"#))
        XCTAssertTrue(jsonString.contains(#""device.id","value":{"stringValue":"xiao-c3-01"}"#))
        XCTAssertTrue(jsonString.contains(#""name":"mcu.wake.count""#))
        XCTAssertTrue(jsonString.contains(#""name":"mcu.phase.duration_us""#))
        XCTAssertTrue(jsonString.contains(#""stringValue":"sensor""#))
        XCTAssertTrue(jsonString.contains(#""stringValue":"compute""#))
        XCTAssertTrue(jsonString.contains(#""stringValue":"epd_refresh""#))
        XCTAssertTrue(jsonString.contains(#""stringValue":"radio""#))
        XCTAssertTrue(jsonString.contains(#""name":"mcu.battery_mv""#))
        XCTAssertTrue(jsonString.contains(#""name":"mcu.ble.rssi""#))
        XCTAssertTrue(jsonString.contains(#""asInt":"-58""#))

        let escapedJSON = XIAOESP32C3Protocol.formatOTLPJSON(
            deviceId: #"xiao-"quoted"\01"#,
            metrics: metrics,
            rssi: -58,
            timeUnixNano: 1_700_000_000_000_000_000
        )
        let escapedData = try XCTUnwrap(escapedJSON.data(using: .utf8))
        XCTAssertNotNil(try JSONSerialization.jsonObject(with: escapedData) as? [String: Any])
    }

    @MainActor
    func testControllerDeduplicatesSameSequenceBurst() {
        let suite = "xiao-esp32c3.tests.\(UUID().uuidString)"
        guard let defaults = UserDefaults(suiteName: suite) else {
            XCTFail("suite")
            return
        }
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = XIAOESP32C3Controller(defaults: defaults)
        let deviceId = UUID()
        let metrics = XIAOESP32C3Metrics(
            seq: 9,
            flags: XIAOESP32C3Protocol.flagDeepSleepWake,
            wakeCount: 9,
            sensorUs: 1_200,
            computeUs: 3_500,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 3_950
        )
        let mfg = XIAOESP32C3Protocol.encodeManufacturerData(metrics)

        XCTAssertTrue(
            controller.ingestManufacturerData(mfg, deviceId: deviceId, deviceName: "XIAO-C3", rssi: -55)
        )
        // Second packet in the same 150 ms burst carries the same `seq` and must be dropped.
        XCTAssertFalse(
            controller.ingestManufacturerData(mfg, deviceId: deviceId, deviceName: "XIAO-C3", rssi: -56)
        )
        XCTAssertEqual(controller.history.count, 1)

        // Next wake increments `seq`.
        var nextMetrics = metrics
        nextMetrics.seq = 10
        nextMetrics.wakeCount = 10
        let nextMfg = XIAOESP32C3Protocol.encodeManufacturerData(nextMetrics)
        XCTAssertTrue(
            controller.ingestManufacturerData(nextMfg, deviceId: deviceId, deviceName: "XIAO-C3", rssi: -52)
        )
        XCTAssertEqual(controller.history.count, 2)
        XCTAssertEqual(controller.latestSample?.metrics.wakeCount, 10)
    }

    @MainActor
    func testResolveMetricsAndBaseURLs() {
        let fromHost = XIAOESP32C3Controller.resolveMetricsURL(from: "https://xiao-otel-xyz.a.run.app")
        XCTAssertEqual(fromHost?.absoluteString, "https://xiao-otel-xyz.a.run.app/v1/metrics")
        if let fromHost {
            let base = XIAOESP32C3Controller.resolveBaseURL(from: fromHost)
            XCTAssertEqual(base?.absoluteString, "https://xiao-otel-xyz.a.run.app/")
        }

        let fromFull = XIAOESP32C3Controller.resolveMetricsURL(from: "http://192.168.1.50:4318/v1/metrics")
        XCTAssertEqual(fromFull?.absoluteString, "http://192.168.1.50:4318/v1/metrics")
    }

    func testOTACommandAndStatusRoundTrip() {
        let sha = String(repeating: "a", count: 64)
        let begin = XIAOESP32C3OTACommand.begin(size: 384_000, sha256: sha)
        XCTAssertEqual(
            XIAOESP32C3Protocol.parseOTACommand(XIAOESP32C3Protocol.encodeOTACommand(begin)),
            begin
        )
        XCTAssertEqual(
            XIAOESP32C3Protocol.parseOTACommand("begin 384000 sha256:\(sha)"),
            begin
        )
        XCTAssertEqual(
            XIAOESP32C3Protocol.parseOTACommand(XIAOESP32C3Protocol.encodeOTACommand(.commit)),
            .commit
        )
        XCTAssertEqual(
            XIAOESP32C3Protocol.parseOTACommand(XIAOESP32C3Protocol.encodeOTACommand(.abort)),
            .abort
        )
        XCTAssertNil(XIAOESP32C3Protocol.parseOTACommand("BEGIN 0 \(sha)"))
        XCTAssertNil(XIAOESP32C3Protocol.parseOTACommand("BEGIN 99999999 \(sha)"))

        let statuses: [XIAOESP32C3OTAStatus] = [
            .idle,
            .ready(total: 384_000),
            .progress(written: 65_536, total: 384_000),
            .ok(sha256: sha),
            .error(message: "sha256 mismatch"),
        ]
        for st in statuses {
            let line = XIAOESP32C3Protocol.formatOTAStatus(st)
            XCTAssertEqual(XIAOESP32C3Protocol.parseOTAStatus(line), st, line)
        }

        let sampleData = Data(repeating: 0x5A, count: 550)
        let chunks = XIAOESP32C3Protocol.chunkFirmware(sampleData, chunkSize: 240)
        XCTAssertEqual(chunks.map(\.count), [240, 240, 70])
    }

    @MainActor
    func testArmedOTATransferOnSimulatedWake() {
        let suite = "xiao-esp32c3.ota-tests.\(UUID().uuidString)"
        guard let defaults = UserDefaults(suiteName: suite) else {
            XCTFail("suite")
            return
        }
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = XIAOESP32C3Controller(defaults: defaults)
        controller.stageSimulatedFirmware()
        XCTAssertNotNil(controller.stagedFirmwareData)
        XCTAssertEqual(controller.otaPhase, .idle)

        controller.armOTAUpdate()
        XCTAssertEqual(controller.otaPhase, .armed)

        controller.injectSimulatedWake()
        XCTAssertEqual(
            controller.otaPhase,
            .completed(sha256: controller.stagedFirmwareSHA256)
        )
    }

    @MainActor
    func testPostMetricsGeneratesFreshKeyInsteadOfReattestingStaleKey() async throws {
        let suite = "xiao-esp32c3.attest-stale.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let store = AppAttestMemoryStore(deviceId: "dev-1", userId: "user-1")
        store.keyId = "stale-already-attested-key"

        let keys = FakeXIAOAttestKeys(generatedKeys: ["fresh-key-1"])
        let http = FakeXIAOHTTP()
        let challengeCounter = LockedInt()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challengeCounter.next()
                return try Self.jsonResponse(#"{"challenge":"c\#(n)","expiresAt":1700000000}"#, status: 200)
            }
            if path.hasSuffix("/v1/register") {
                let body = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                let keyId = body?["keyId"] as? String ?? ""
                XCTAssertEqual(keyId, "fresh-key-1")
                return try Self.jsonResponse(
                    #"{"userId":"user-1","deviceId":"dev-1","keyId":"\#(keyId)","unattested":false,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/metrics") {
                XCTAssertEqual(request.value(forHTTPHeaderField: "X-Apple-App-Attest-Key-Id"), "fresh-key-1")
                XCTAssertNotNil(request.value(forHTTPHeaderField: "X-Apple-App-Attest-Assertion"))
                return try Self.jsonResponse(#"{"status":"accepted"}"#, status: 202)
            }
            return try Self.jsonResponse(#"{"error":"unexpected"}"#, status: 500)
        }

        let controller = XIAOESP32C3Controller(
            defaults: defaults,
            attestKeys: keys,
            attestStore: store,
            http: http
        )
        let metricsURL = try XCTUnwrap(URL(string: "https://xiao-otel.example.test/v1/metrics"))
        let baseURL = try XCTUnwrap(URL(string: "https://xiao-otel.example.test/"))

        let status = try await controller.postMetrics(
            body: Data(#"{"resourceMetrics":[]}"#.utf8),
            metricsURL: metricsURL,
            baseURL: baseURL,
            authorizeWithAppAttest: true
        )
        XCTAssertEqual(status, 202)
        XCTAssertEqual(store.keyId, "fresh-key-1")
        XCTAssertEqual(keys.attestedKeys, ["fresh-key-1"])
    }

    @MainActor
    func testPostMetricsReattestsAndRetriesOnceAfter401() async throws {
        let suite = "xiao-esp32c3.attest-401.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let store = AppAttestMemoryStore(deviceId: "dev-2", userId: "user-2")
        let keys = FakeXIAOAttestKeys(generatedKeys: ["key-1", "key-2"])
        let http = FakeXIAOHTTP()
        let challengeCounter = LockedInt()
        let metricsAttempts = LockedInt()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challengeCounter.next()
                return try Self.jsonResponse(#"{"challenge":"c\#(n)","expiresAt":1700000000}"#, status: 200)
            }
            if path.hasSuffix("/v1/register") {
                let body = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                let keyId = body?["keyId"] as? String ?? ""
                return try Self.jsonResponse(
                    #"{"userId":"user-2","deviceId":"dev-2","keyId":"\#(keyId)","unattested":false,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/metrics") {
                let attempt = metricsAttempts.next()
                let keyId = request.value(forHTTPHeaderField: "X-Apple-App-Attest-Key-Id")
                if attempt == 1 {
                    XCTAssertEqual(keyId, "key-1")
                    return try Self.jsonResponse(#"{"error":"unknown key"}"#, status: 401)
                }
                XCTAssertEqual(keyId, "key-2")
                return try Self.jsonResponse(#"{"status":"accepted"}"#, status: 202)
            }
            return try Self.jsonResponse(#"{"error":"unexpected"}"#, status: 500)
        }

        let controller = XIAOESP32C3Controller(
            defaults: defaults,
            attestKeys: keys,
            attestStore: store,
            http: http
        )
        let metricsURL = try XCTUnwrap(URL(string: "https://xiao-otel.example.test/v1/metrics"))
        let baseURL = try XCTUnwrap(URL(string: "https://xiao-otel.example.test/"))

        let status = try await controller.postMetrics(
            body: Data(#"{"resourceMetrics":[]}"#.utf8),
            metricsURL: metricsURL,
            baseURL: baseURL,
            authorizeWithAppAttest: true
        )
        XCTAssertEqual(status, 202)
        XCTAssertEqual(store.keyId, "key-2")
        XCTAssertEqual(keys.attestedKeys, ["key-1", "key-2"])
    }

    private static func jsonResponse(_ body: String, status: Int) throws -> (Data, URLResponse) {
        let url = try XCTUnwrap(URL(string: "https://xiao-otel.example.test"))
        let response = try XCTUnwrap(HTTPURLResponse(
            url: url,
            statusCode: status,
            httpVersion: "HTTP/1.1",
            headerFields: ["Content-Type": "application/json"]
        ))
        return (Data(body.utf8), response)
    }
}

private final class FakeXIAOHTTP: AppAttestHTTPClient, @unchecked Sendable {
    var onRequest: @Sendable (URLRequest) throws -> (Data, URLResponse) = { _ in
        throw URLError(.badServerResponse)
    }

    func data(for request: URLRequest) async throws -> (Data, URLResponse) {
        try onRequest(request)
    }
}

private final class FakeXIAOAttestKeys: AppAttestKeyGenerating, @unchecked Sendable {
    let isSupported = true
    private let lock = NSLock()
    private var generatedKeys: [String]
    private var attestedSet: Set<String> = ["stale-already-attested-key"]
    private var attestedOrder: [String] = []

    init(generatedKeys: [String]) {
        self.generatedKeys = generatedKeys
    }

    var attestedKeys: [String] {
        lock.lock()
        defer { lock.unlock() }
        return attestedOrder
    }

    func generateKey() async throws -> String {
        popNextKey()
    }

    func attestKey(_ keyId: String, clientDataHash _: Data) async throws -> Data {
        try recordAttestation(keyId)
    }

    func generateAssertion(_: String, clientDataHash _: Data) async throws -> Data {
        Data([0x02])
    }

    private func popNextKey() -> String {
        lock.lock()
        defer { lock.unlock() }
        return generatedKeys.isEmpty ? "generated-fallback" : generatedKeys.removeFirst()
    }

    private func recordAttestation(_ keyId: String) throws -> Data {
        lock.lock()
        defer { lock.unlock() }
        if attestedSet.contains(keyId) {
            throw NSError(domain: DCError.errorDomain, code: DCError.invalidInput.rawValue)
        }
        attestedSet.insert(keyId)
        attestedOrder.append(keyId)
        return Data([0x01])
    }
}

private final class LockedInt: @unchecked Sendable {
    private let lock = NSLock()
    private var value = 0

    func next() -> Int {
        lock.lock()
        defer { lock.unlock() }
        value += 1
        return value
    }
}

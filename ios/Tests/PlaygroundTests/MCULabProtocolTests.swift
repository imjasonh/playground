import DeviceCheck
import XCTest
@testable import Playground

final class MCULabProtocolTests: XCTestCase {
    func testManufacturerDataRoundTrip() {
        let metrics = MCULabMetrics(
            seq: 42,
            flags: MCULabProtocol.flagDeepSleepWake | MCULabProtocol.flagEpdPartial,
            wakeCount: 1_024,
            sensorUs: 1_450,
            computeUs: 3_820,
            epdRefreshUs: 320_500,
            radioUs: 152_000,
            batteryMv: 3_910
        )
        let mfg = MCULabProtocol.encodeManufacturerData(metrics)
        XCTAssertEqual(mfg.count, MCULabProtocol.manufacturerDataLength)
        XCTAssertEqual(mfg[0], 0xFF)
        XCTAssertEqual(mfg[1], 0xFF)

        let decoded = MCULabProtocol.decodeManufacturerData(mfg)
        XCTAssertEqual(decoded, metrics)
        XCTAssertEqual(decoded?.isDeepSleepWake, true)
        XCTAssertEqual(decoded?.isEpdPartialRefresh, true)
        XCTAssertEqual(decoded?.isEpdAttached, false)
        XCTAssertEqual(decoded?.isBrownoutReset, false)
        XCTAssertEqual(decoded?.totalActiveUs, 477_770)
    }

    func testDecodeRejectsWrongCompanyIDAndShortBuffers() {
        let metrics = MCULabMetrics(
            seq: 1,
            flags: 0,
            wakeCount: 1,
            sensorUs: 900,
            computeUs: 2_100,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 4_000
        )
        var mfg = MCULabProtocol.encodeManufacturerData(metrics)
        mfg[0] = 0x4C
        mfg[1] = 0x00
        XCTAssertNil(MCULabProtocol.decodeManufacturerData(mfg))
        XCTAssertNil(MCULabProtocol.decodeManufacturerData(Data([0xFF, 0xFF, 0x01])))
    }

    func testFormatStatusLineMatchesFirmware() {
        let metrics = MCULabMetrics(
            seq: 12,
            flags: MCULabProtocol.flagDeepSleepWake | MCULabProtocol.flagEpdPartial,
            wakeCount: 12,
            sensorUs: 1_340,
            computeUs: 4_120,
            epdRefreshUs: 320_000,
            radioUs: 149_500,
            batteryMv: 3_880
        )
        XCTAssertEqual(
            MCULabProtocol.formatStatusLine(metrics),
            "seq=12 wake=12 sensor_us=1340 compute_us=4120 epd_us=320000 radio_us=149500 batt_mv=3880 flags=0x05"
        )
    }

    func testFormatOTLPJSONContainsAllMetricsAndPhases() throws {
        let metrics = MCULabMetrics(
            seq: 3,
            flags: MCULabProtocol.flagDeepSleepWake,
            wakeCount: 15,
            sensorUs: 1_100,
            computeUs: 3_400,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 3_890
        )
        let jsonString = MCULabProtocol.formatOTLPJSON(
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

        let escapedJSON = MCULabProtocol.formatOTLPJSON(
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

        let controller = MCULabController(defaults: defaults)
        let deviceId = UUID()
        let metrics = MCULabMetrics(
            seq: 9,
            flags: MCULabProtocol.flagDeepSleepWake,
            wakeCount: 9,
            sensorUs: 1_200,
            computeUs: 3_500,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 3_950
        )
        let mfg = MCULabProtocol.encodeManufacturerData(metrics)

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
        let nextMfg = MCULabProtocol.encodeManufacturerData(nextMetrics)
        XCTAssertTrue(
            controller.ingestManufacturerData(nextMfg, deviceId: deviceId, deviceName: "XIAO-C3", rssi: -52)
        )
        XCTAssertEqual(controller.history.count, 2)
        XCTAssertEqual(controller.latestSample?.metrics.wakeCount, 10)
    }

    @MainActor
    func testResolveMetricsAndBaseURLs() {
        let fromHost = MCULabController.resolveMetricsURL(from: "https://xiao-otel-xyz.a.run.app")
        XCTAssertEqual(fromHost?.absoluteString, "https://xiao-otel-xyz.a.run.app/v1/metrics")
        if let fromHost {
            let base = MCULabController.resolveBaseURL(from: fromHost)
            XCTAssertEqual(base?.absoluteString, "https://xiao-otel-xyz.a.run.app/")
        }

        let fromFull = MCULabController.resolveMetricsURL(from: "http://192.168.1.50:4318/v1/metrics")
        XCTAssertEqual(fromFull?.absoluteString, "http://192.168.1.50:4318/v1/metrics")
    }

    func testOTACommandAndStatusRoundTrip() {
        let sha = String(repeating: "a", count: 64)
        let begin = MCULabOTACommand.begin(size: 384_000, sha256: sha)
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(begin)),
            begin
        )
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand("begin 384000 sha256:\(sha)"),
            begin
        )
        let beginDeflate = MCULabOTACommand.begin(size: 775_328, sha256: sha, compression: .deflate)
        XCTAssertEqual(
            MCULabProtocol.encodeOTACommand(beginDeflate),
            "BEGIN 775328 \(sha) deflate"
        )
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(beginDeflate)),
            beginDeflate
        )
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand("BEGIN 775328 \(sha) DEFLATE"),
            beginDeflate
        )
        XCTAssertNil(MCULabProtocol.parseOTACommand("BEGIN 775328 \(sha) lz4"))
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(.commit)),
            .commit
        )
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(.abort)),
            .abort
        )
        XCTAssertNil(MCULabProtocol.parseOTACommand("BEGIN 0 \(sha)"))
        XCTAssertNil(MCULabProtocol.parseOTACommand("BEGIN 99999999 \(sha)"))

        let statuses: [MCULabOTAStatus] = [
            .idle,
            .ready(total: 384_000),
            .progress(written: 65_536, total: 384_000),
            .ok(sha256: sha),
            .error(message: "sha256 mismatch"),
        ]
        for st in statuses {
            let line = MCULabProtocol.formatOTAStatus(st)
            XCTAssertEqual(MCULabProtocol.parseOTAStatus(line), st, line)
        }

        let sampleData = Data(repeating: 0x5A, count: 550)
        let chunks = MCULabProtocol.chunkFirmware(sampleData, chunkSize: 240)
        XCTAssertEqual(chunks.map(\.count), [240, 240, 70])

        let compressible = Data((0..<4096).map { UInt8($0 % 37) })
        let deflated = MCULabProtocol.deflateCompress(compressible)
        XCTAssertNotNil(deflated)
        XCTAssertLessThan(deflated?.count ?? compressible.count, compressible.count / 2)
        if let deflated {
            let restored = try? (deflated as NSData).decompressed(using: .zlib) as Data
            XCTAssertEqual(restored, compressible)
        }
    }

    func testOTAReportMetricsAndOTLPFormatting() throws {
        let start = Date(timeIntervalSince1970: 1_700_000_000)
        let end = start.addingTimeInterval(35.0)
        let report = MCULabOTAReport(
            board: .waveshareEPD75,
            app: .maze,
            imageName: "waveshare-epd75-maze@deadbee",
            sha256: String(repeating: "b", count: 64),
            compression: .deflate,
            outcome: "ok",
            rawBytes: 775_328,
            wireBytes: 440_000,
            packetCount: 937,
            chunkSize: 480,
            startedAt: start,
            completedAt: end,
            connectMs: 400,
            eraseMs: 6_200,
            streamMs: 28_100,
            commitMs: 300,
            totalMs: 35_000,
            mcuBatteryStartMv: 3_840,
            mcuBatteryEndMv: 3_815,
            phoneBatteryStartPct: 52,
            phoneBatteryEndPct: 51
        )
        XCTAssertTrue(report.isSuccess)
        XCTAssertEqual(report.compressionSavedPct, 43)
        XCTAssertGreaterThan(report.effectiveBytesPerSec, 27_000)
        XCTAssertGreaterThan(report.wireBytesPerSec, 15_000)
        XCTAssertEqual(report.avgRttMs, 28_100.0 / 937.0, accuracy: 0.01)
        XCTAssertEqual(report.mcuBatteryDeltaMv, -25)
        XCTAssertEqual(report.phoneBatteryDeltaPct, -1)
        XCTAssertGreaterThan(report.estimatedMcuEnergyMj, 10_000)

        let metricsJSON = MCULabProtocol.formatOTAOTLPMetricsJSON(
            deviceId: "epd75-01",
            report: report,
            timeUnixNano: 1_700_000_035_000_000_000
        )
        let metricsObj = try JSONSerialization.jsonObject(with: Data(metricsJSON.utf8)) as? [String: Any]
        XCTAssertNotNil(metricsObj?["resourceMetrics"])
        XCTAssertTrue(metricsJSON.contains("mcu.ota.duration_ms"))
        XCTAssertTrue(metricsJSON.contains("mcu.ota.throughput_bps"))
        XCTAssertTrue(metricsJSON.contains("mcu.ota.energy_mj"))
        XCTAssertTrue(metricsJSON.contains("mcu.ota.battery_delta_mv"))
        XCTAssertTrue(metricsJSON.contains("mcu.ota.phone_battery_pct"))

        let traceJSON = MCULabProtocol.formatOTAOTLPTraceJSON(
            traceId: String(repeating: "1", count: 32),
            rootSpanId: String(repeating: "2", count: 16),
            deviceId: "epd75-01",
            report: report
        )
        let traceObj = try JSONSerialization.jsonObject(with: Data(traceJSON.utf8)) as? [String: Any]
        XCTAssertNotNil(traceObj?["resourceSpans"])
        XCTAssertTrue(traceJSON.contains("ota.update waveshare-epd75-maze"))
        XCTAssertTrue(traceJSON.contains("ota.connect"))
        XCTAssertTrue(traceJSON.contains("ota.erase"))
        XCTAssertTrue(traceJSON.contains("ota.stream"))
        XCTAssertTrue(traceJSON.contains("ota.commit"))
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

        let controller = MCULabController(defaults: defaults)
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

        let keys = FakeMCULabAttestKeys(generatedKeys: ["fresh-key-1"])
        let http = FakeMCULabHTTP()
        let challengeCounter = LockedInt()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challengeCounter.next()
                return try Self.jsonResponse(#"{"challenge":"c\#(n)","expiresAt":1700000000}"#, status: 200)
            }
            if path.hasSuffix("/v1/token") {
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

        let controller = MCULabController(
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
        let keys = FakeMCULabAttestKeys(generatedKeys: ["key-1", "key-2"])
        let http = FakeMCULabHTTP()
        let challengeCounter = LockedInt()
        let metricsAttempts = LockedInt()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challengeCounter.next()
                return try Self.jsonResponse(#"{"challenge":"c\#(n)","expiresAt":1700000000}"#, status: 200)
            }
            if path.hasSuffix("/v1/token") {
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

        let controller = MCULabController(
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

    func testWakeProfileDecodeAndOTLPTraceJSON() throws {
        let rawProfile = """
        {"v":1,"wake":7,"seq":7,"free_heap":210944,"min_heap":198400,"stack_hw":3072,"cycles":7420000,"spans":[{"name":"boot.init","parent":"wake","start_us":0,"dur_us":420},{"name":"epd.busy_wait","parent":"epd_refresh","start_us":4800,"dur_us":32000}],"pcs":[{"pc":"0x42001a40","hits":14}]}
        """
        let profile = try XCTUnwrap(MCULabProtocol.decodeWakeProfile(Data(rawProfile.utf8)))
        XCTAssertEqual(profile.wakeCount, 7)
        XCTAssertEqual(profile.freeHeapBytes, 210_944)
        XCTAssertEqual(profile.spans.count, 2)
        XCTAssertEqual(profile.pcSamples.first?.pc, "0x42001a40")

        let metrics = MCULabMetrics(
            seq: 7,
            flags: MCULabProtocol.flagDeepSleepWake | MCULabProtocol.flagEpdPartial,
            wakeCount: 7,
            sensorUs: 1_200,
            computeUs: 3_400,
            epdRefreshUs: 320_000,
            radioUs: 150_000,
            batteryMv: 3_910
        )
        let metricsJSON = MCULabProtocol.formatOTLPJSON(
            deviceId: "xiao-c3-01",
            metrics: metrics,
            rssi: -54,
            timeUnixNano: 1_700_000_000_000_000_000,
            profile: profile
        )
        XCTAssertTrue(metricsJSON.contains(#""name":"mcu.heap.free_bytes""#))
        XCTAssertTrue(metricsJSON.contains(#""name":"mcu.cpu.cycles""#))
        XCTAssertNotNil(try JSONSerialization.jsonObject(with: Data(metricsJSON.utf8)) as? [String: Any])

        let traceJSON = MCULabProtocol.formatOTLPTraceJSON(
            traceId: "0123456789abcdef0123456789abcdef",
            rootSpanId: "1111111111111111",
            deviceId: "xiao-c3-01",
            metrics: metrics,
            rssi: -54,
            timeUnixNano: 1_700_000_000_000_000_000,
            profile: profile
        )
        let parsed = try XCTUnwrap(JSONSerialization.jsonObject(with: Data(traceJSON.utf8)) as? [String: Any])
        XCTAssertNotNil(parsed["resourceSpans"])
        XCTAssertTrue(traceJSON.contains(#""name":"xiao.wake #7""#))
        XCTAssertTrue(traceJSON.contains(#""name":"epd.busy_wait""#))
        XCTAssertTrue(traceJSON.contains(#""name":"pc.hotspot""#))
        XCTAssertTrue(traceJSON.contains(#""0x42001a40""#))
    }

    @MainActor
    func testPostTracesWithAppAttest() async throws {
        let suite = "xiao-esp32c3.traces.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let store = AppAttestMemoryStore(deviceId: "dev-t", userId: "user-t")
        let keys = FakeMCULabAttestKeys(generatedKeys: ["trace-key-1"])
        let http = FakeMCULabHTTP()
        let challengeCounter = LockedInt()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challengeCounter.next()
                return try Self.jsonResponse(#"{"challenge":"c\#(n)","expiresAt":1700000000}"#, status: 200)
            }
            if path.hasSuffix("/v1/token") {
                return try Self.jsonResponse(
                    #"{"userId":"user-t","deviceId":"dev-t","keyId":"trace-key-1","unattested":false,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/traces") {
                XCTAssertEqual(request.value(forHTTPHeaderField: "X-Apple-App-Attest-Key-Id"), "trace-key-1")
                let cdB64 = try XCTUnwrap(request.value(forHTTPHeaderField: "X-Apple-App-Attest-Client-Data"))
                let cdData = try XCTUnwrap(Data(base64Encoded: cdB64))
                let cdObj = try JSONSerialization.jsonObject(with: cdData) as? [String: Any]
                XCTAssertEqual(cdObj?["action"] as? String, "traces")
                return try Self.jsonResponse(#"{"acceptedSpans":5}"#, status: 200)
            }
            return try Self.jsonResponse(#"{"error":"unexpected"}"#, status: 500)
        }

        let controller = MCULabController(
            defaults: defaults,
            attestKeys: keys,
            attestStore: store,
            http: http
        )
        let baseURL = try XCTUnwrap(URL(string: "https://xiao-otel.example.test/"))
        let tracesURL = MCULabController.resolveTracesURL(from: baseURL)
        let status = try await controller.postTraces(
            body: Data(#"{"resourceSpans":[]}"#.utf8),
            tracesURL: tracesURL,
            baseURL: baseURL,
            authorizeWithAppAttest: true
        )
        XCTAssertEqual(status, 200)
    }

    @MainActor
    func testPullLatestFirmwareFromGHCRResolvesCommitSHA() async throws {
        let suite = "mcu-lab.ghcr-sha.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let shaBuilding = String(repeating: "a", count: 40)
        let shaPublished = String(repeating: "b", count: 40)
        var hdr = [UInt8](repeating: 0, count: 24)
        hdr[0] = 0xE9
        hdr[12] = 0x05 // CHIP_ID_ESP32C3 = 0x0005 (little-endian)
        hdr[13] = 0x00
        let firmwareBytes = Data(hdr) + Data(repeating: 0x5A, count: 64)
        let expectedDigest = "sha256:\(MCULabProtocol.sha256Hex(firmwareBytes))"

        let http = FakeMCULabHTTP()
        http.onRequest = { request in
            let urlString = request.url?.absoluteString ?? ""
            if urlString.contains("api.github.com/repos/imjasonh/playground/commits") {
                return try Self.jsonResponse(
                    #"[{"sha":"\#(shaBuilding)"},{"sha":"\#(shaPublished)"}]"#,
                    status: 200
                )
            }
            if urlString.contains("ghcr.io/token") {
                return try Self.jsonResponse(#"{"token":"anon-tok"}"#, status: 200)
            }
            if urlString.hasSuffix("/manifests/\(shaBuilding)") {
                return try Self.jsonResponse(#"{"errors":[{"code":"MANIFEST_UNKNOWN"}]}"#, status: 404)
            }
            if urlString.hasSuffix("/manifests/\(shaPublished)") {
                return try Self.jsonResponse(
                    #"{"layers":[{"mediaType":"application/octet-stream","digest":"\#(expectedDigest)"}]}"#,
                    status: 200
                )
            }
            if urlString.hasSuffix("/blobs/\(expectedDigest)") {
                let url = try XCTUnwrap(request.url)
                let resp = try XCTUnwrap(HTTPURLResponse(
                    url: url,
                    statusCode: 200,
                    httpVersion: "HTTP/1.1",
                    headerFields: ["Content-Type": "application/octet-stream"]
                ))
                return (firmwareBytes, resp)
            }
            return try Self.jsonResponse(#"{"error":"unexpected \(urlString)"}"#, status: 500)
        }

        let controller = MCULabController(
            defaults: defaults,
            attestKeys: FakeMCULabAttestKeys(generatedKeys: []),
            attestStore: AppAttestMemoryStore(deviceId: "dev-ota", userId: "user-ota"),
            http: http
        )
        let target = MCULabFirmwareTarget(board: .xiaoESP32C3, app: .base)
        await controller.pullLatestFirmwareFromGHCR(target: target)

        XCTAssertEqual(controller.stagedFirmwareData, firmwareBytes)
        XCTAssertTrue(controller.stagedFirmwareName.hasPrefix("xiao-esp32c3-base@\(shaPublished.prefix(7))"))

        // Cross-chip safety check: ESP32-C3 binary must be rejected for Waveshare ESP32 board.
        XCTAssertNotNil(MCULabProtocol.validateESPImageHeader(firmwareBytes, expectedChipID: MCULabBoard.waveshareEPD75.chipID))
        XCTAssertNil(MCULabProtocol.validateESPImageHeader(firmwareBytes, expectedChipID: MCULabBoard.xiaoESP32C3.chipID))
    }

    func testOTLPPayloadsUseBoardSpecificServiceName() {
        let epdFlags: UInt8 = MCULabProtocol.flagEpdAttached
            | (MCULabBoard.waveshareEPD75.boardID << 4)
        let epdMetrics = MCULabMetrics(
            seq: 3,
            flags: epdFlags,
            wakeCount: 11,
            sensorUs: 120,
            computeUs: 9_500,
            epdRefreshUs: 1_800_000,
            radioUs: 500_000,
            batteryMv: 5000
        )
        let metricsJSON = MCULabProtocol.formatOTLPJSON(
            deviceId: "epd-uuid-1",
            metrics: epdMetrics,
            rssi: -48,
            timeUnixNano: 1_700_000_000_000_000_000
        )
        XCTAssertTrue(metricsJSON.contains(#""service.name","value":{"stringValue":"waveshare-epd75"}"#))
        XCTAssertTrue(metricsJSON.contains(#""device.id","value":{"stringValue":"epd-uuid-1"}"#))

        let traceJSON = MCULabProtocol.formatOTLPTraceJSON(
            traceId: "0123456789abcdef0123456789abcdef",
            rootSpanId: "0123456789abcdef",
            deviceId: "epd-uuid-1",
            metrics: epdMetrics,
            rssi: -48,
            timeUnixNano: 1_700_000_000_000_000_000
        )
        XCTAssertTrue(traceJSON.contains(#""service.name","value":{"stringValue":"waveshare-epd75"}"#))
        XCTAssertTrue(traceJSON.contains(#""name":"waveshare-epd75.wake #11""#))
    }

    @MainActor
    func testArmOTAUpdateRejectsMismatchedChipAfterSwitchingTarget() throws {
        let suite = "mcu-lab.arm-guard.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = MCULabController(defaults: defaults)
        var xiaoImage = Data(repeating: 0x00, count: 64)
        xiaoImage[0] = 0xE9
        xiaoImage[12] = 0x05 // ESP32-C3 chip_id = 0x0005

        controller.selectedBoard = .xiaoESP32C3
        controller.selectedApp = .bench
        controller.stageFirmware(data: xiaoImage, name: "xiao-esp32c3-bench.bin")
        XCTAssertNotNil(controller.stagedFirmwareData)

        // Switching board after staging must reset incompatible app to .base and block arming the wrong chip binary.
        controller.selectedBoard = .waveshareEPD75
        XCTAssertEqual(controller.selectedApp, .base)
        XCTAssertEqual(MCULabBoard.waveshareEPD75.compatibleApps, [.base, .maze, .gzipBench])
        XCTAssertEqual(MCULabBoard.xiaoESP32C3.compatibleApps, [.base, .bench, .gzipBench])
        controller.armOTAUpdate()
        if case .failed = controller.otaPhase {
            // Expected
        } else {
            XCTFail("Expected .failed OTA phase when arming ESP32-C3 binary for waveshare-epd75, got \(controller.otaPhase)")
        }
    }

    @MainActor
    func testMultiDeviceIngestionDeduplicatesIndependently() throws {
        let suite = "mcu-lab.multi-dev.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = MCULabController(defaults: defaults)
        controller.updateForwardingEnabled(false)
        controller.saveCollectDetailedProfile(false)

        let xiaoId = UUID()
        let epdId = UUID()

        let xiaoMfg = MCULabProtocol.encodeManufacturerData(
            MCULabMetrics(
                seq: 1,
                flags: MCULabProtocol.flagDeepSleepWake | (MCULabBoard.xiaoESP32C3.boardID << 4),
                wakeCount: 1,
                sensorUs: 1000,
                computeUs: 2000,
                epdRefreshUs: 3000,
                radioUs: 4000,
                batteryMv: 3900
            )
        )
        let epdMfg = MCULabProtocol.encodeManufacturerData(
            MCULabMetrics(
                seq: 1,
                flags: MCULabProtocol.flagEpdAttached | (MCULabBoard.waveshareEPD75.boardID << 4),
                wakeCount: 1,
                sensorUs: 100,
                computeUs: 8000,
                epdRefreshUs: 1_500_000,
                radioUs: 500_000,
                batteryMv: 5000
            )
        )

        XCTAssertTrue(controller.ingestManufacturerData(xiaoMfg, deviceId: xiaoId, deviceName: "XIAO-C3", rssi: -60))
        // Duplicate seq 1 from XIAO is ignored, while seq 1 from EPD-75 is accepted.
        XCTAssertFalse(controller.ingestManufacturerData(xiaoMfg, deviceId: xiaoId, deviceName: "XIAO-C3", rssi: -61))
        XCTAssertTrue(controller.ingestManufacturerData(epdMfg, deviceId: epdId, deviceName: "EPD-75", rssi: -45))
        XCTAssertFalse(controller.ingestManufacturerData(epdMfg, deviceId: epdId, deviceName: "EPD-75", rssi: -46))

        XCTAssertEqual(controller.history.count, 2)
        XCTAssertEqual(controller.history[0].deviceId, epdId)
        XCTAssertEqual(controller.history[1].deviceId, xiaoId)
    }

    func testCRC32AndFramedOTAChunksAndResumableReadyStatus() {
        XCTAssertEqual(MCULabProtocol.crc32(Data("123456789".utf8)), 0xCBF4_3926)
        XCTAssertEqual(MCULabProtocol.crc32(Data()), 0x0000_0000)

        let readyResumed = MCULabOTAStatus.ready(total: 384_000, offset: 65_536)
        let formatted = MCULabProtocol.formatOTAStatus(readyResumed)
        XCTAssertEqual(formatted, "READY total=384000 offset=65536")
        XCTAssertEqual(MCULabProtocol.parseOTAStatus(formatted), readyResumed)

        let firmware = Data((0..<1000).map { UInt8($0 % 251) })
        let framed = MCULabProtocol.chunkFirmwareFramed(firmware, startingAt: 500, maxPacketBytes: 210)
        XCTAssertEqual(framed.count, 3)
        XCTAssertEqual(framed[0].offset, 500)
        XCTAssertEqual(framed[0].payloadCount, 200)
        XCTAssertEqual(framed[0].frame[0], 0x4F) // 'O'
        XCTAssertEqual(framed[0].frame[1], 0x54) // 'T'
        XCTAssertEqual(framed.map(\.payloadCount).reduce(0, +), 500)
    }

    func testBlobReassemblerReassemblesOutOfOrderChunks() {
        let part0 = Data("hello ".utf8)
        let part1 = Data("world!".utf8)
        var frame0 = Data([0x4D, 0x43, 0x00, 0x00, 0x02, 0x00])
        frame0.append(part0)
        var frame1 = Data([0x4D, 0x43, 0x01, 0x00, 0x02, 0x00])
        frame1.append(part1)

        var reasm = MCULabBlobReassembler()
        XCTAssertNil(reasm.push(frame1))
        let complete = reasm.push(frame0)
        XCTAssertEqual(complete, Data("hello world!".utf8))
    }

    func testWakeProfileBuildIDIncludedInTraceJSON() throws {
        let json = """
        {"v":1,"wake":9,"seq":9,"board":"xiao-esp32c3","chip":"esp32c3","app":"xiao-esp32c3","git_sha":"\(String(repeating: "a", count: 40))","build_id":"\(String(repeating: "b", count: 40))","free_heap":200000,"min_heap":190000,"stack_hw":4096,"cycles":1000,"spans":[],"pcs":[]}
        """
        let profile = try XCTUnwrap(MCULabProtocol.decodeWakeProfile(Data(json.utf8)))
        XCTAssertEqual(profile.buildId, String(repeating: "b", count: 40))

        let metrics = MCULabMetrics(seq: 9, flags: 0, wakeCount: 9, sensorUs: 100, computeUs: 200, epdRefreshUs: 300, radioUs: 400, batteryMv: 3850)
        let trace = MCULabProtocol.formatOTLPTraceJSON(
            traceId: String(repeating: "1", count: 32),
            rootSpanId: String(repeating: "2", count: 16),
            deviceId: "dev-1",
            metrics: metrics,
            rssi: -50,
            timeUnixNano: 1_700_000_000_000_000_000,
            profile: profile
        )
        XCTAssertTrue(trace.contains(#""key":"mcu.build_id","value":{"stringValue":"\#(String(repeating: "b", count: 40))""#))
    }

    @MainActor
    func testPullLatestFirmwareFromGHCRPrefersPublishWorkflowRuns() async throws {
        let suite = "mcu-lab.ghcr-workflow.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let mergeSHA = String(repeating: "e", count: 40)
        var hdr = [UInt8](repeating: 0, count: 24)
        hdr[0] = 0xE9
        hdr[12] = 0x00 // CHIP_ID_ESP32 = 0x0000
        hdr[13] = 0x00
        let firmwareBytes = Data(hdr) + Data(repeating: 0x3C, count: 64)
        let expectedDigest = "sha256:\(MCULabProtocol.sha256Hex(firmwareBytes))"

        let http = FakeMCULabHTTP()
        http.onRequest = { request in
            let urlString = request.url?.absoluteString ?? ""
            if urlString.contains("actions/workflows/mcu-lab-publish.yml/runs") {
                return try Self.jsonResponse(
                    #"{"workflow_runs":[{"head_sha":"\#(mergeSHA)"},{"head_sha":"\#(mergeSHA)"}]}"#,
                    status: 200
                )
            }
            if urlString.contains("ghcr.io/token") {
                return try Self.jsonResponse(#"{"token":"anon-tok"}"#, status: 200)
            }
            if urlString.hasSuffix("/manifests/\(mergeSHA)") {
                return try Self.jsonResponse(
                    #"{"layers":[{"mediaType":"application/octet-stream","digest":"\#(expectedDigest)"}]}"#,
                    status: 200
                )
            }
            if urlString.hasSuffix("/blobs/\(expectedDigest)") {
                let url = try XCTUnwrap(request.url)
                let resp = try XCTUnwrap(HTTPURLResponse(
                    url: url,
                    statusCode: 200,
                    httpVersion: "HTTP/1.1",
                    headerFields: ["Content-Type": "application/octet-stream"]
                ))
                return (firmwareBytes, resp)
            }
            return try Self.jsonResponse(#"{"error":"unexpected \(urlString)"}"#, status: 500)
        }

        let controller = MCULabController(
            defaults: defaults,
            attestKeys: FakeMCULabAttestKeys(generatedKeys: []),
            attestStore: AppAttestMemoryStore(deviceId: "dev-ota", userId: "user-ota"),
            http: http
        )
        let target = MCULabFirmwareTarget(board: .waveshareEPD75, app: .maze)
        await controller.pullLatestFirmwareFromGHCR(target: target)

        XCTAssertEqual(controller.stagedFirmwareData, firmwareBytes)
        XCTAssertTrue(controller.stagedFirmwareName.hasPrefix("waveshare-epd75-maze@\(mergeSHA.prefix(7))"))
    }

    @MainActor
    func testAutoForwardThrottlesPerDeviceWithinMinInterval() async throws {
        let suite = "mcu-lab.otel-throttle.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let metricsPostCount = LockedInt()
        let http = FakeMCULabHTTP()
        http.onRequest = { request in
            let urlString = request.url?.absoluteString ?? ""
            if urlString.hasSuffix("/v1/metrics") {
                _ = metricsPostCount.next()
                return try Self.jsonResponse(#"{}"#, status: 200)
            }
            if urlString.hasSuffix("/v1/traces") {
                return try Self.jsonResponse(#"{"resolvedSymbols":{}}"#, status: 200)
            }
            return try Self.jsonResponse(#"{"error":"unexpected \(urlString)"}"#, status: 500)
        }

        let controller = MCULabController(
            defaults: defaults,
            attestKeys: FakeMCULabAttestKeys(generatedKeys: []),
            attestStore: AppAttestMemoryStore(deviceId: "dev-throttle", userId: "user-throttle"),
            http: http
        )
        controller.updateEndpoint("https://xiao-otel.example.test/v1/metrics")
        controller.updateUseAppAttest(false)
        controller.updateForwardingEnabled(true)

        let devA = UUID()
        let devB = UUID()
        let t0 = Date(timeIntervalSince1970: 1_700_000_000)

        let m1 = MCULabMetrics(seq: 1, flags: 0x20, wakeCount: 1, sensorUs: 10, computeUs: 0, epdRefreshUs: 0, radioUs: 500, batteryMv: 5000)
        let m2 = MCULabMetrics(seq: 2, flags: 0x20, wakeCount: 2, sensorUs: 10, computeUs: 0, epdRefreshUs: 0, radioUs: 500, batteryMv: 5000)
        let m3 = MCULabMetrics(seq: 3, flags: 0x20, wakeCount: 3, sensorUs: 10, computeUs: 0, epdRefreshUs: 0, radioUs: 500, batteryMv: 5000)

        // First wake from devA forwards.
        XCTAssertTrue(controller.ingestManufacturerData(MCULabProtocol.encodeManufacturerData(m1), deviceId: devA, deviceName: "EPD-75", rssi: -50, now: t0))
        // Second wake from devA only 2 s later is throttled (< 5.5 s).
        XCTAssertTrue(controller.ingestManufacturerData(MCULabProtocol.encodeManufacturerData(m2), deviceId: devA, deviceName: "EPD-75", rssi: -50, now: t0.addingTimeInterval(2.0)))
        // Wake from devB at +2 s is NOT throttled by devA.
        XCTAssertTrue(controller.ingestManufacturerData(MCULabProtocol.encodeManufacturerData(m1), deviceId: devB, deviceName: "XIAO-C3", rssi: -55, now: t0.addingTimeInterval(2.0)))
        // Third wake from devA at +6 s forwards again.
        XCTAssertTrue(controller.ingestManufacturerData(MCULabProtocol.encodeManufacturerData(m3), deviceId: devA, deviceName: "EPD-75", rssi: -50, now: t0.addingTimeInterval(6.0)))

        try await Task.sleep(for: .milliseconds(150))
        XCTAssertEqual(controller.forwardedCount, 3)
        XCTAssertEqual(metricsPostCount.current, 3)
    }

    func testGzipBenchTargetsAndAppOTelMetricsAndAttrs() throws {
        XCTAssertTrue(MCULabBoard.xiaoESP32C3.compatibleApps.contains(.gzipBench))
        XCTAssertTrue(MCULabBoard.waveshareEPD75.compatibleApps.contains(.gzipBench))
        XCTAssertEqual(
            MCULabFirmwareTarget(board: .xiaoESP32C3, app: .gzipBench).ghcrRepo,
            "imjasonh/playground/xiao-esp32c3-gzip-bench"
        )
        XCTAssertEqual(
            MCULabFirmwareTarget(board: .waveshareEPD75, app: .gzipBench).ghcrRepo,
            "imjasonh/playground/waveshare-epd75-gzip-bench"
        )

        let rawJSON = """
        {"v":1,"wake":4,"seq":4,"board":"waveshare-epd75","chip":"esp32","app":"waveshare-epd75-gzip-bench","free_heap":205000,"min_heap":192000,"stack_hw":4096,"cycles":12000000,"spans":[{"name":"gzip.inflate.json_otel","parent":"compute","start_us":100,"dur_us":3200,"attrs":{"corpus":"json_otel","impl":"esp32_rom_miniz"}}],"pcs":[{"pc":"0x40060050","hits":12}],"attrs":{"gzip.impl":"esp32_rom_miniz","gzip.deflate_status":"oom"},"metrics":[{"name":"gzip.inflate_bps","val":2100000,"unit":"By/s","attrs":{"corpus":"json_otel","impl":"esp32_rom_miniz"}},{"name":"gzip.inflate_bps","val":5400000,"unit":"By/s","attrs":{"corpus":"rle_epd","impl":"esp32_rom_miniz"}},{"name":"gzip.deflate_oom","val":1,"unit":"1","attrs":{"impl":"esp32_rom_miniz"}}]}
        """
        let profile = try XCTUnwrap(MCULabProtocol.decodeWakeProfile(Data(rawJSON.utf8)))
        XCTAssertEqual(profile.attrs?["gzip.impl"], "esp32_rom_miniz")
        XCTAssertEqual(profile.spans.first?.attrs?["corpus"], "json_otel")
        XCTAssertEqual(profile.metrics?.count, 3)

        let m = MCULabMetrics(seq: 4, flags: 0x20, wakeCount: 4, sensorUs: 50, computeUs: 50_000, epdRefreshUs: 0, radioUs: 500, batteryMv: 5000)
        let metricsJSON = MCULabProtocol.formatOTLPJSON(
            deviceId: "epd-01",
            metrics: m,
            rssi: -52,
            timeUnixNano: 1_700_000_000_000_000_000,
            profile: profile
        )
        XCTAssertTrue(metricsJSON.contains(#""name":"mcu.app.gzip.inflate_bps""#))
        XCTAssertTrue(metricsJSON.contains(#""asInt":"2100000""#))
        XCTAssertTrue(metricsJSON.contains(#""asInt":"5400000""#))
        XCTAssertTrue(metricsJSON.contains(#""name":"mcu.app.gzip.deflate_oom""#))
        XCTAssertTrue(metricsJSON.contains(#""key":"impl","value":{"stringValue":"esp32_rom_miniz"}"#))
        _ = try JSONSerialization.jsonObject(with: Data(metricsJSON.utf8))

        let traceJSON = MCULabProtocol.formatOTLPTraceJSON(
            traceId: String(repeating: "a", count: 32),
            rootSpanId: String(repeating: "b", count: 16),
            deviceId: "epd-01",
            metrics: m,
            rssi: -52,
            timeUnixNano: 1_700_000_000_000_000_000,
            profile: profile
        )
        XCTAssertTrue(traceJSON.contains(#""key":"gzip.impl","value":{"stringValue":"esp32_rom_miniz"}"#))
        XCTAssertTrue(traceJSON.contains(#""key":"gzip.deflate_status","value":{"stringValue":"oom"}"#))
        XCTAssertTrue(traceJSON.contains(#""key":"corpus","value":{"stringValue":"json_otel"}"#))
        _ = try JSONSerialization.jsonObject(with: Data(traceJSON.utf8))
    }

    @MainActor
    func testDeclarativeAppCommandsDecodeEncodeAndArm() throws {
        let rawJSON = """
        {"v":1,"wake":2,"seq":2,"board":"xiao-esp32c3","chip":"esp32c3","app":"xiao-esp32c3-gzip-bench","free_heap":220000,"min_heap":210000,"stack_hw":4096,"cycles":1000,"spans":[],"pcs":[],"cmds":[{"id":"run","label":"Run Benchmark","count":10}]}
        """
        let profile = try XCTUnwrap(MCULabProtocol.decodeWakeProfile(Data(rawJSON.utf8)))
        XCTAssertEqual(profile.commands, [
            MCULabAppCommandSpec(id: "run", label: "Run Benchmark", defaultCount: 10),
        ])

        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "run", count: 1), "run")
        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "run", count: 10), "run 10")
        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "run", count: 0), "run")
        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "run", count: 999), "run 100")

        let suite = "mcu-lab.app-cmd.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = MCULabController(defaults: defaults)
        let devId = UUID()
        let cmd = try XCTUnwrap(profile.commands?.first)
        controller.armAppCommand(cmd, count: 15, deviceId: devId)
        XCTAssertEqual(
            controller.pendingAppCommand,
            MCULabController.PendingAppCommand(deviceId: devId, id: "run", label: "Run Benchmark", count: 15)
        )
        XCTAssertTrue(controller.appCommandStatus.contains("Run Benchmark"))

        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "RUN", count: 10), "run 10")
        XCTAssertEqual(MCULabProtocol.encodeAppCommand(id: "RUN", count: 1), "run")

        controller.cancelAppCommand()
        XCTAssertNil(controller.pendingAppCommand)

        let runMetrics = MCULabMetrics(
            seq: 2,
            flags: MCULabProtocol.flagDeepSleepWake,
            wakeCount: 2,
            sensorUs: 100,
            computeUs: 5_000,
            epdRefreshUs: 0,
            radioUs: 200_000,
            batteryMv: 4_100
        )
        let runData = MCULabProtocol.encodeManufacturerData(runMetrics)
        var midProfile = profile
        midProfile.wakeCount = 2
        midProfile.seq = 2
        midProfile.attrs = ["mcu.cmd": "run", "mcu.cmd.run": "3/10"]
        XCTAssertTrue(
            controller.ingestManufacturerData(
                runData,
                deviceId: devId,
                deviceName: "MCU-LAB",
                rssi: -55,
                profile: midProfile
            )
        )
        XCTAssertEqual(controller.appCommandStatus, "Received run 3/10 of 'run'…")

        let finalMetrics = MCULabMetrics(
            seq: 3,
            flags: MCULabProtocol.flagDeepSleepWake,
            wakeCount: 3,
            sensorUs: 100,
            computeUs: 5_000,
            epdRefreshUs: 0,
            radioUs: 200_000,
            batteryMv: 4_100
        )
        let finalData = MCULabProtocol.encodeManufacturerData(finalMetrics)
        var finalProfile = profile
        finalProfile.wakeCount = 3
        finalProfile.seq = 3
        finalProfile.attrs = ["mcu.cmd": "run", "mcu.cmd.run": "10/10"]
        XCTAssertTrue(
            controller.ingestManufacturerData(
                finalData,
                deviceId: devId,
                deviceName: "MCU-LAB",
                rssi: -55,
                profile: finalProfile
            )
        )
        XCTAssertEqual(controller.appCommandStatus, "Completed 'run' (10/10).")
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

private final class FakeMCULabHTTP: AppAttestHTTPClient, @unchecked Sendable {
    var onRequest: @Sendable (URLRequest) throws -> (Data, URLResponse) = { _ in
        throw URLError(.badServerResponse)
    }

    func data(for request: URLRequest) async throws -> (Data, URLResponse) {
        try onRequest(request)
    }
}

private final class FakeMCULabAttestKeys: AppAttestKeyGenerating, @unchecked Sendable {
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

    var current: Int {
        lock.lock()
        defer { lock.unlock() }
        return value
    }
}

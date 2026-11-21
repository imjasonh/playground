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
}

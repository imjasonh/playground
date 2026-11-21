import Foundation

/// 24-byte profiling telemetry payload unpacked from BLE Manufacturer Specific Data (`0xFFFF`).
///
/// Mirrors `AdvMetrics` in `xiao-esp32c3/src/protocol.rs`.
struct XIAOESP32C3Metrics: Equatable, Identifiable {
    var seq: UInt8
    var flags: UInt8
    var wakeCount: UInt32
    var sensorUs: UInt32
    var computeUs: UInt32
    var epdRefreshUs: UInt32
    var radioUs: UInt32
    var batteryMv: UInt16

    var id: String {
        "\(wakeCount)-\(seq)"
    }

    var isDeepSleepWake: Bool {
        (flags & XIAOESP32C3Protocol.flagDeepSleepWake) != 0
    }

    var isEpdAttached: Bool {
        (flags & XIAOESP32C3Protocol.flagEpdAttached) != 0
    }

    var isEpdPartialRefresh: Bool {
        (flags & XIAOESP32C3Protocol.flagEpdPartial) != 0
    }

    var isBrownoutReset: Bool {
        (flags & XIAOESP32C3Protocol.flagBrownoutReset) != 0
    }

    /// Total active awake duration across all four measured phases in microseconds.
    var totalActiveUs: UInt64 {
        UInt64(sensorUs) + UInt64(computeUs) + UInt64(epdRefreshUs) + UInt64(radioUs)
    }

    /// Estimated energy consumed by this wake cycle in microjoules (µJ) using
    /// typical XIAO ESP32C3 active current profiles.
    var estimatedEnergyUj: UInt64 {
        let vMv = batteryMv > 0 ? UInt64(batteryMv) : 3700
        let microampSeconds = UInt64(sensorUs) * 28
            + UInt64(computeUs) * 32
            + UInt64(epdRefreshUs) * 38
            + UInt64(radioUs) * 85
        return (microampSeconds * vMv) / 1_000_000
    }

    /// E-paper refresh mode label (`Partial LUT` vs `Full LUT`).
    var epdRefreshModeLabel: String {
        isEpdPartialRefresh ? "Partial LUT" : "Full LUT"
    }
}

/// Shared wire format and OTLP JSON builder with `xiao-esp32c3/src/protocol.rs`.
enum XIAOESP32C3Protocol {
    static let deviceName = "XIAO-C3"
    static let companyID: UInt16 = 0xFFFF
    static let payloadLength = 24
    static let manufacturerDataLength = 2 + payloadLength

    static let flagDeepSleepWake: UInt8 = 1 << 0
    static let flagEpdAttached: UInt8 = 1 << 1
    static let flagEpdPartial: UInt8 = 1 << 2
    static let flagBrownoutReset: UInt8 = 1 << 3

    static let defaultOtelEndpoint = "http://192.168.1.50:4318/v1/metrics"

    /// Decode a 26-byte Manufacturer Specific Data buffer (`0xFFFF` company ID + 24-byte payload).
    static func decodeManufacturerData(_ data: Data) -> XIAOESP32C3Metrics? {
        guard data.count == manufacturerDataLength else {
            return nil
        }
        let company = data.readUInt16LE(at: 0)
        guard company == companyID else {
            return nil
        }
        return decodePayload(data.subdata(in: 2..<manufacturerDataLength))
    }

    /// Encode a 26-byte Manufacturer Specific Data buffer (`0xFFFF` company ID + 24-byte payload).
    static func encodeManufacturerData(_ metrics: XIAOESP32C3Metrics) -> Data {
        var out = Data(capacity: manufacturerDataLength)
        out.appendUInt16LE(companyID)
        out.append(encodePayload(metrics))
        return out
    }

    /// Decode a 24-byte little-endian payload into `XIAOESP32C3Metrics`.
    static func decodePayload(_ data: Data) -> XIAOESP32C3Metrics? {
        guard data.count == payloadLength else {
            return nil
        }
        return XIAOESP32C3Metrics(
            seq: data[data.startIndex],
            flags: data[data.startIndex + 1],
            wakeCount: data.readUInt32LE(at: 2),
            sensorUs: data.readUInt32LE(at: 6),
            computeUs: data.readUInt32LE(at: 10),
            epdRefreshUs: data.readUInt32LE(at: 14),
            radioUs: data.readUInt32LE(at: 18),
            batteryMv: data.readUInt16LE(at: 22)
        )
    }

    /// Encode `XIAOESP32C3Metrics` into its 24-byte little-endian payload.
    static func encodePayload(_ metrics: XIAOESP32C3Metrics) -> Data {
        var out = Data(capacity: payloadLength)
        out.append(metrics.seq)
        out.append(metrics.flags)
        out.appendUInt32LE(metrics.wakeCount)
        out.appendUInt32LE(metrics.sensorUs)
        out.appendUInt32LE(metrics.computeUs)
        out.appendUInt32LE(metrics.epdRefreshUs)
        out.appendUInt32LE(metrics.radioUs)
        out.appendUInt16LE(metrics.batteryMv)
        return out
    }

    /// Format a single-line summary matching `format_status_line` in `xiao-esp32c3/src/protocol.rs`.
    static func formatStatusLine(_ m: XIAOESP32C3Metrics) -> String {
        let flagsHex = String(format: "0x%02x", m.flags)
        return "seq=\(m.seq) wake=\(m.wakeCount) sensor_us=\(m.sensorUs) compute_us=\(m.computeUs) epd_us=\(m.epdRefreshUs) radio_us=\(m.radioUs) batt_mv=\(m.batteryMv) flags=\(flagsHex)"
    }

    /// Build a valid OTLP/HTTP v1 JSON metrics payload (`application/json`).
    static func formatOTLPJSON(
        deviceId: String,
        metrics: XIAOESP32C3Metrics,
        rssi: Int,
        timeUnixNano: UInt64
    ) -> String {
        let ts = String(timeUnixNano)
        return """
        {"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"xiao-esp32c3"}},{"key":"device.id","value":{"stringValue":"\(deviceId)"}}]},"scopeMetrics":[{"metrics":[{"name":"mcu.wake.count","gauge":{"dataPoints":[{"asInt":"\(metrics.wakeCount)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.phase.duration_us","gauge":{"dataPoints":[{"asInt":"\(metrics.sensorUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"sensor"}}]},{"asInt":"\(metrics.computeUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"compute"}}]},{"asInt":"\(metrics.epdRefreshUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"epd_refresh"}}]},{"asInt":"\(metrics.radioUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"radio"}}]}]}},{"name":"mcu.battery_mv","gauge":{"dataPoints":[{"asInt":"\(metrics.batteryMv)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.ble.rssi","gauge":{"dataPoints":[{"asInt":"\(rssi)","timeUnixNano":"\(ts)"}]}}]}]}]}
        """
    }

    /// Format a microsecond duration for display (`1,450 µs` or `320.5 ms`).
    static func formatDurationUs(_ us: UInt32) -> String {
        if us >= 10_000 {
            let ms = Double(us) / 1_000.0
            return String(format: "%.1f ms", ms)
        }
        return "\(us) µs"
    }
}

private extension Data {
    func readUInt16LE(at offset: Int) -> UInt16 {
        let base = startIndex + offset
        return UInt16(self[base]) | (UInt16(self[base + 1]) << 8)
    }

    func readUInt32LE(at offset: Int) -> UInt32 {
        let base = startIndex + offset
        let b0 = UInt32(self[base])
        let b1 = UInt32(self[base + 1]) << 8
        let b2 = UInt32(self[base + 2]) << 16
        let b3 = UInt32(self[base + 3]) << 24
        return b0 | b1 | b2 | b3
    }

    mutating func appendUInt16LE(_ value: UInt16) {
        append(UInt8(truncatingIfNeeded: value))
        append(UInt8(truncatingIfNeeded: value >> 8))
    }

    mutating func appendUInt32LE(_ value: UInt32) {
        append(UInt8(truncatingIfNeeded: value))
        append(UInt8(truncatingIfNeeded: value >> 8))
        append(UInt8(truncatingIfNeeded: value >> 16))
        append(UInt8(truncatingIfNeeded: value >> 24))
    }
}

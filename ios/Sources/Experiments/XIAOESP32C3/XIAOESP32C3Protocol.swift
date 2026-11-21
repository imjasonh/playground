import CryptoKit
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

/// Control command written by the iPhone to the XIAO BLE GATT OTA control characteristic.
enum XIAOESP32C3OTACommand: Equatable {
    case begin(size: UInt32, sha256: String)
    case commit
    case abort
}

/// Status notification sent by the XIAO on the BLE GATT OTA status characteristic.
enum XIAOESP32C3OTAStatus: Equatable {
    case idle
    case ready(total: UInt32)
    case progress(written: UInt32, total: UInt32)
    case ok(sha256: String)
    case error(message: String)
}

/// Shared wire format, BLE GATT OTA protocol, and OTLP JSON builder with `xiao-esp32c3/src/protocol.rs`.
enum XIAOESP32C3Protocol {
    static let deviceName = "XIAO-C3"
    static let companyID: UInt16 = 0xFFFF
    static let payloadLength = 24
    static let manufacturerDataLength = 2 + payloadLength

    static let otaServiceUUIDString = "4FAFC301-1FB5-459E-8FCC-C5C9C331914B"
    static let otaControlUUIDString = "BEB5483E-36E1-4688-B7F5-EA07361BC301"
    static let otaDataUUIDString = "BEB5483E-36E1-4688-B7F5-EA07361BC302"
    static let otaStatusUUIDString = "1A3C0001-36E1-4688-B7F5-EA07361BC303"
    static let otaSlotBytes: UInt32 = 0x1F_0000

    static let flagDeepSleepWake: UInt8 = 1 << 0
    static let flagEpdAttached: UInt8 = 1 << 1
    static let flagEpdPartial: UInt8 = 1 << 2
    static let flagBrownoutReset: UInt8 = 1 << 3

    static let otelEndpointInfoPlistKey = "XIAOOtelEndpoint"
    static let fallbackOtelEndpoint = "https://xiao-otel-965235416369.us-central1.run.app/v1/metrics"
    static var defaultOtelEndpoint: String {
        if let configured = Bundle.main.object(forInfoDictionaryKey: otelEndpointInfoPlistKey) as? String {
            let trimmed = configured.trimmingCharacters(in: .whitespacesAndNewlines)
            if !trimmed.isEmpty {
                return trimmed
            }
        }
        return fallbackOtelEndpoint
    }
    static let defaultGHCRRepo = "imjasonh/playground/xiao-esp32c3"
    static let defaultGHCRTag = "latest"

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

    /// Encode an OTA control command matching `encode_ota_command` in `xiao-esp32c3/src/protocol.rs`.
    static func encodeOTACommand(_ command: XIAOESP32C3OTACommand) -> String {
        switch command {
        case .begin(let size, let sha256):
            return "BEGIN \(size) \(sha256.lowercased())"
        case .commit:
            return "COMMIT"
        case .abort:
            return "ABORT"
        }
    }

    /// Parse an OTA control command string.
    static func parseOTACommand(_ raw: String) -> XIAOESP32C3OTACommand? {
        let parts = raw.split(whereSeparator: \.isWhitespace).map(String.init)
        guard let head = parts.first?.uppercased() else {
            return nil
        }
        switch head {
        case "COMMIT" where parts.count == 1:
            return .commit
        case "ABORT" where parts.count == 1:
            return .abort
        case "BEGIN" where parts.count == 3:
            guard let size = UInt32(parts[1]), size > 0, size <= otaSlotBytes else {
                return nil
            }
            var sha = parts[2].lowercased()
            if sha.hasPrefix("sha256:") {
                sha = String(sha.dropFirst("sha256:".count))
            }
            guard sha.count == 64, sha.allSatisfy(\.isHexDigit) else {
                return nil
            }
            return .begin(size: size, sha256: sha)
        default:
            return nil
        }
    }

    /// Format an OTA status line matching `format_ota_status` in `xiao-esp32c3/src/protocol.rs`.
    static func formatOTAStatus(_ status: XIAOESP32C3OTAStatus) -> String {
        switch status {
        case .idle:
            return "IDLE"
        case .ready(let total):
            return "READY total=\(total)"
        case .progress(let written, let total):
            return "PROGRESS written=\(written) total=\(total)"
        case .ok(let sha256):
            return "OK sha256=\(sha256.lowercased())"
        case .error(let message):
            return "ERR \(message)"
        }
    }

    /// Parse an OTA status notification line from `OTA_STATUS_UUID`.
    static func parseOTAStatus(_ raw: String) -> XIAOESP32C3OTAStatus? {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed == "IDLE" {
            return .idle
        }
        if trimmed.hasPrefix("ERR ") {
            let msg = trimmed.dropFirst(4).trimmingCharacters(in: .whitespaces)
            return .error(message: msg)
        }
        if trimmed.hasPrefix("READY ") {
            let rest = trimmed.dropFirst(6).trimmingCharacters(in: .whitespaces)
            guard rest.hasPrefix("total="),
                  let total = UInt32(rest.dropFirst("total=".count))
            else {
                return nil
            }
            return .ready(total: total)
        }
        if trimmed.hasPrefix("OK ") {
            let rest = trimmed.dropFirst(3).trimmingCharacters(in: .whitespaces)
            guard rest.hasPrefix("sha256=") else {
                return nil
            }
            let sha = String(rest.dropFirst("sha256=".count)).lowercased()
            guard sha.count == 64, sha.allSatisfy(\.isHexDigit) else {
                return nil
            }
            return .ok(sha256: sha)
        }
        if trimmed.hasPrefix("PROGRESS ") {
            let rest = trimmed.dropFirst("PROGRESS ".count)
            var written: UInt32?
            var total: UInt32?
            for part in rest.split(whereSeparator: \.isWhitespace).map(String.init) {
                if part.hasPrefix("written=") {
                    written = UInt32(part.dropFirst("written=".count))
                } else if part.hasPrefix("total=") {
                    total = UInt32(part.dropFirst("total=".count))
                }
            }
            guard let written, let total else {
                return nil
            }
            return .progress(written: written, total: total)
        }
        return nil
    }

    /// Compute the lowercase hex SHA-256 digest of a firmware binary.
    static func sha256Hex(_ data: Data) -> String {
        SHA256.hash(data: data).map { String(format: "%02x", $0) }.joined()
    }

    /// Split a firmware binary into BLE MTU-sized chunks (default 240 bytes).
    static func chunkFirmware(_ data: Data, chunkSize: Int = 240) -> [Data] {
        let step = max(chunkSize, 20)
        var chunks: [Data] = []
        chunks.reserveCapacity((data.count + step - 1) / step)
        var offset = 0
        while offset < data.count {
            let end = min(offset + step, data.count)
            chunks.append(data.subdata(in: offset..<end))
            offset = end
        }
        return chunks
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
        let safeDeviceId = escapeJSONString(deviceId)
        return """
        {"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"xiao-esp32c3"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeMetrics":[{"metrics":[{"name":"mcu.wake.count","gauge":{"dataPoints":[{"asInt":"\(metrics.wakeCount)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.phase.duration_us","gauge":{"dataPoints":[{"asInt":"\(metrics.sensorUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"sensor"}}]},{"asInt":"\(metrics.computeUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"compute"}}]},{"asInt":"\(metrics.epdRefreshUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"epd_refresh"}}]},{"asInt":"\(metrics.radioUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"radio"}}]}]}},{"name":"mcu.battery_mv","gauge":{"dataPoints":[{"asInt":"\(metrics.batteryMv)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.ble.rssi","gauge":{"dataPoints":[{"asInt":"\(rssi)","timeUnixNano":"\(ts)"}]}}]}]}]}
        """
    }

    private static func escapeJSONString(_ value: String) -> String {
        var out = ""
        out.reserveCapacity(value.count)
        for scalar in value.unicodeScalars {
            switch scalar {
            case "\"":
                out.append("\\\"")
            case "\\":
                out.append("\\\\")
            case "\0"..<" ":
                continue
            default:
                out.unicodeScalars.append(scalar)
            }
        }
        return out
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

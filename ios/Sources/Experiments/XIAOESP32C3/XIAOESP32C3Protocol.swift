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

/// A single sub-phase timing span recorded on the XIAO ESP32C3 MCU.
struct XIAOESP32C3ProfileSpan: Equatable, Identifiable, Decodable {
    var name: String
    var parent: String
    var startUs: UInt32
    var durationUs: UInt32

    var id: String { "\(parent).\(name).\(startUs)" }

    enum CodingKeys: String, CodingKey {
        case name, parent
        case startUs = "start_us"
        case durationUs = "dur_us"
    }
}

/// A sampled program-counter hotspot (`pc` hex address + sample hits).
struct XIAOESP32C3PCSample: Equatable, Identifiable, Decodable {
    var pc: String
    var hits: UInt16

    var id: String { pc }
}

/// A server-symbolized PC hotspot returned by `xiao-otel` (`POST /v1/traces`).
struct XIAOESP32C3ResolvedSymbol: Equatable, Decodable {
    var function: String?
    var file: String?
    var line: Int?

    var displayLabel: String {
        let fn = function ?? ""
        if let file, let line, line > 0 {
            return fn.isEmpty ? "\(file):\(line)" : "\(fn) (\(file):\(line))"
        }
        return fn
    }
}

/// Detailed per-wake profiling snapshot pulled over BLE GATT (`PROFILE_CHAR_UUID`).
struct XIAOESP32C3WakeProfile: Equatable, Decodable {
    var version: UInt8
    var wakeCount: UInt32
    var seq: UInt8
    var gitSha: String? = nil
    var freeHeapBytes: UInt32
    var minFreeHeapBytes: UInt32
    var stackHighWaterBytes: UInt32
    var cpuCycles: UInt64
    var spans: [XIAOESP32C3ProfileSpan]
    var pcSamples: [XIAOESP32C3PCSample]

    enum CodingKeys: String, CodingKey {
        case version = "v"
        case wakeCount = "wake"
        case seq
        case gitSha = "git_sha"
        case freeHeapBytes = "free_heap"
        case minFreeHeapBytes = "min_heap"
        case stackHighWaterBytes = "stack_hw"
        case cpuCycles = "cycles"
        case spans
        case pcSamples = "pcs"
    }
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
    static let profileCharUUIDString = "1A3C0002-36E1-4688-B7F5-EA07361BC303"
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
    static let defaultGitHubRepo = "imjasonh/playground"
    static let defaultFirmwarePath = "xiao-esp32c3"

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

    /// Decode a `WakeProfile` JSON payload read from `PROFILE_CHAR_UUID`.
    static func decodeWakeProfile(_ data: Data) -> XIAOESP32C3WakeProfile? {
        try? JSONDecoder().decode(XIAOESP32C3WakeProfile.self, from: data)
    }

    /// Generate a realistic simulated `WakeProfile` for bench / Simulator testing.
    static func simulatedWakeProfile(for metrics: XIAOESP32C3Metrics) -> XIAOESP32C3WakeProfile {
        let bootUs: UInt32 = 420
        let sensorStart = bootUs
        let computeStart = sensorStart + metrics.sensorUs
        let epdStart = computeStart + metrics.computeUs
        let spiUs = min(metrics.epdRefreshUs / 10, 2_800)
        let busyUs = metrics.epdRefreshUs > spiUs ? metrics.epdRefreshUs - spiUs : 0
        let totalActiveUs = UInt64(bootUs) + UInt64(metrics.sensorUs) + UInt64(metrics.computeUs) + UInt64(metrics.epdRefreshUs)
        return XIAOESP32C3WakeProfile(
            version: 1,
            wakeCount: metrics.wakeCount,
            seq: metrics.seq,
            freeHeapBytes: 210_944,
            minFreeHeapBytes: 198_400,
            stackHighWaterBytes: 3_072,
            cpuCycles: totalActiveUs * 160,
            spans: [
                XIAOESP32C3ProfileSpan(name: "boot.init", parent: "wake", startUs: 0, durationUs: bootUs),
                XIAOESP32C3ProfileSpan(name: "sensor.adc_filter", parent: "sensor", startUs: sensorStart, durationUs: metrics.sensorUs),
                XIAOESP32C3ProfileSpan(name: "compute.epd_render", parent: "compute", startUs: computeStart, durationUs: metrics.computeUs),
                XIAOESP32C3ProfileSpan(name: "epd.spi_transfer", parent: "epd_refresh", startUs: epdStart, durationUs: spiUs),
                XIAOESP32C3ProfileSpan(name: "epd.busy_wait", parent: "epd_refresh", startUs: epdStart + spiUs, durationUs: busyUs),
            ],
            pcSamples: [
                XIAOESP32C3PCSample(pc: "0x42001a40", hits: 14),
                XIAOESP32C3PCSample(pc: "0x42003c18", hits: 6),
                XIAOESP32C3PCSample(pc: "0x42000e84", hits: 3),
            ]
        )
    }

    /// Generate a lowercase hex string of `byteCount` random bytes (never all zeros).
    static func randomHex(byteCount: Int) -> String {
        var bytes = [UInt8](repeating: 0, count: max(byteCount, 1))
        for idx in bytes.indices {
            bytes[idx] = UInt8.random(in: 0...255)
        }
        if bytes.allSatisfy({ $0 == 0 }) {
            bytes[bytes.count - 1] = 1
        }
        return bytes.map { String(format: "%02x", $0) }.joined()
    }

    /// Build a valid OTLP/HTTP v1 JSON metrics payload (`application/json`).
    static func formatOTLPJSON(
        deviceId: String,
        metrics: XIAOESP32C3Metrics,
        rssi: Int,
        timeUnixNano: UInt64,
        profile: XIAOESP32C3WakeProfile? = nil
    ) -> String {
        let ts = String(timeUnixNano)
        let safeDeviceId = escapeJSONString(deviceId)
        var extraMetrics = ""
        if let profile {
            extraMetrics = """
            ,{"name":"mcu.heap.free_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.freeHeapBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.heap.min_free_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.minFreeHeapBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.stack.high_water_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.stackHighWaterBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.cpu.cycles","gauge":{"dataPoints":[{"asInt":"\(profile.cpuCycles)","timeUnixNano":"\(ts)"}]}}
            """
        }
        return """
        {"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"xiao-esp32c3"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeMetrics":[{"metrics":[{"name":"mcu.wake.count","gauge":{"dataPoints":[{"asInt":"\(metrics.wakeCount)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.phase.duration_us","gauge":{"dataPoints":[{"asInt":"\(metrics.sensorUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"sensor"}}]},{"asInt":"\(metrics.computeUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"compute"}}]},{"asInt":"\(metrics.epdRefreshUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"epd_refresh"}}]},{"asInt":"\(metrics.radioUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"radio"}}]}]}},{"name":"mcu.battery_mv","gauge":{"dataPoints":[{"asInt":"\(metrics.batteryMv)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.ble.rssi","gauge":{"dataPoints":[{"asInt":"\(rssi)","timeUnixNano":"\(ts)"}]}}\(extraMetrics)]}]}]}
        """
    }

    /// Build a valid OTLP/HTTP v1 JSON trace payload (`ExportTraceServiceRequest`) representing
    /// the wake waterfall (`xiao.wake` root span + 4 MCU phase spans + optional firmware sub-phase spans).
    static func formatOTLPTraceJSON(
        traceId: String,
        rootSpanId: String,
        deviceId: String,
        metrics: XIAOESP32C3Metrics,
        rssi: Int,
        timeUnixNano: UInt64,
        profile: XIAOESP32C3WakeProfile? = nil
    ) -> String {
        let totalActiveNs = metrics.totalActiveUs * 1_000
        let wakeStartNs = timeUnixNano > totalActiveNs ? timeUnixNano - totalActiveNs : timeUnixNano
        var wakeEndNs = wakeStartNs + totalActiveNs
        if let profile {
            for sub in profile.spans {
                let subEnd = wakeStartNs + UInt64(sub.startUs + sub.durationUs) * 1_000
                if subEnd > wakeEndNs {
                    wakeEndNs = subEnd
                }
            }
        }

        let sensorSpanId = randomHex(byteCount: 8)
        let computeSpanId = randomHex(byteCount: 8)
        let epdSpanId = randomHex(byteCount: 8)
        let radioSpanId = randomHex(byteCount: 8)

        let sensorStart = wakeStartNs
        let sensorEnd = sensorStart + UInt64(metrics.sensorUs) * 1_000
        let computeStart = sensorEnd
        let computeEnd = computeStart + UInt64(metrics.computeUs) * 1_000
        let epdStart = computeEnd
        let epdEnd = epdStart + UInt64(metrics.epdRefreshUs) * 1_000
        let radioStart = epdEnd
        let radioEnd = radioStart + UInt64(metrics.radioUs) * 1_000

        var rootAttrs: [String] = [
            #"{"key":"mcu.wake.count","value":{"intValue":"\#(metrics.wakeCount)"}}"#,
            #"{"key":"mcu.battery_mv","value":{"intValue":"\#(metrics.batteryMv)"}}"#,
            #"{"key":"mcu.ble.rssi","value":{"intValue":"\#(rssi)"}}"#,
            #"{"key":"mcu.epd.mode","value":{"stringValue":"\#(metrics.epdRefreshModeLabel)"}}"#,
        ]
        var rootEvents: [String] = []
        if let profile {
            if let gitSha = profile.gitSha, !gitSha.isEmpty {
                rootAttrs.append(#"{"key":"mcu.git_sha","value":{"stringValue":"\#(escapeJSONString(gitSha))"}}"#)
            }
            rootAttrs.append(#"{"key":"mcu.heap.free_bytes","value":{"intValue":"\#(profile.freeHeapBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.heap.min_free_bytes","value":{"intValue":"\#(profile.minFreeHeapBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.stack.high_water_bytes","value":{"intValue":"\#(profile.stackHighWaterBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.cpu.cycles","value":{"intValue":"\#(profile.cpuCycles)"}}"#)
            for sample in profile.pcSamples {
                let safePc = escapeJSONString(sample.pc)
                rootEvents.append(
                    #"{"timeUnixNano":"\#(wakeEndNs)","name":"pc.hotspot","attributes":[{"key":"pc","value":{"stringValue":"\#(safePc)"}},{"key":"hits","value":{"intValue":"\#(sample.hits)"}}]}"#
                )
            }
        }

        var spans: [String] = [
            formatSpanJSON(
                traceId: traceId,
                spanId: rootSpanId,
                parentSpanId: nil,
                name: "xiao.wake #\(metrics.wakeCount)",
                startNs: wakeStartNs,
                endNs: wakeEndNs,
                attrs: rootAttrs,
                events: rootEvents
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: sensorSpanId,
                parentSpanId: rootSpanId,
                name: "mcu.sensor",
                startNs: sensorStart,
                endNs: sensorEnd
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: computeSpanId,
                parentSpanId: rootSpanId,
                name: "mcu.compute",
                startNs: computeStart,
                endNs: computeEnd
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: epdSpanId,
                parentSpanId: rootSpanId,
                name: "mcu.epd_refresh",
                startNs: epdStart,
                endNs: epdEnd,
                attrs: [#"{"key":"mcu.epd.mode","value":{"stringValue":"\#(metrics.epdRefreshModeLabel)"}}"#]
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: radioSpanId,
                parentSpanId: rootSpanId,
                name: "mcu.radio",
                startNs: radioStart,
                endNs: radioEnd
            ),
        ]

        if let profile {
            let parentMap: [String: String] = [
                "wake": rootSpanId,
                "sensor": sensorSpanId,
                "compute": computeSpanId,
                "epd_refresh": epdSpanId,
                "radio": radioSpanId,
            ]
            for sub in profile.spans {
                let parentId = parentMap[sub.parent] ?? rootSpanId
                let subStart = wakeStartNs + UInt64(sub.startUs) * 1_000
                let subEnd = subStart + UInt64(sub.durationUs) * 1_000
                spans.append(
                    formatSpanJSON(
                        traceId: traceId,
                        spanId: randomHex(byteCount: 8),
                        parentSpanId: parentId,
                        name: sub.name,
                        startNs: subStart,
                        endNs: subEnd
                    )
                )
            }
        }

        let safeDeviceId = escapeJSONString(deviceId)
        return """
        {"resourceSpans":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"xiao-esp32c3"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeSpans":[{"spans":[\(spans.joined(separator: ","))]}]}]}
        """
    }

    private static func formatSpanJSON(
        traceId: String,
        spanId: String,
        parentSpanId: String?,
        name: String,
        startNs: UInt64,
        endNs: UInt64,
        attrs: [String] = [],
        events: [String] = []
    ) -> String {
        var parts: [String] = [
            #""traceId":"\#(escapeJSONString(traceId))""#,
            #""spanId":"\#(escapeJSONString(spanId))""#,
        ]
        if let parentSpanId {
            parts.append(#""parentSpanId":"\#(escapeJSONString(parentSpanId))""#)
        }
        parts.append(#""name":"\#(escapeJSONString(name))""#)
        parts.append(#""startTimeUnixNano":"\#(startNs)""#)
        parts.append(#""endTimeUnixNano":"\#(endNs)""#)
        if !attrs.isEmpty {
            parts.append(#""attributes":[\#(attrs.joined(separator: ","))]"#)
        }
        if !events.isEmpty {
            parts.append(#""events":[\#(events.joined(separator: ","))]"#)
        }
        return "{\(parts.joined(separator: ","))}"
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

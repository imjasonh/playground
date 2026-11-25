import CryptoKit
import Foundation

/// 24-byte profiling telemetry payload unpacked from BLE Manufacturer Specific Data (`0xFFFF`).
///
/// Mirrors `AdvMetrics` in `mcu-lab/src/protocol.rs`.
struct MCULabMetrics: Equatable, Identifiable {
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
        (flags & MCULabProtocol.flagDeepSleepWake) != 0
    }

    var isEpdAttached: Bool {
        (flags & MCULabProtocol.flagEpdAttached) != 0
    }

    var isEpdPartialRefresh: Bool {
        (flags & MCULabProtocol.flagEpdPartial) != 0
    }

    var isBrownoutReset: Bool {
        (flags & MCULabProtocol.flagBrownoutReset) != 0
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

    /// Board ID encoded in the upper 4 bits of `flags` (`0` = legacy XIAO, `1` = XIAO ESP32-C3, `2` = Waveshare EPD-75).
    var boardID: UInt8 {
        (flags >> 4) & 0x0F
    }

    /// Hardware board inferred from `boardID` in the BLE advertisement.
    var inferredBoard: MCULabBoard {
        switch boardID {
        case MCULabBoard.waveshareEPD75.boardID:
            return .waveshareEPD75
        default:
            return .xiaoESP32C3
        }
    }
}

/// Wire compression mode for a BLE OTA transfer.
enum MCULabOTACompression: String, Equatable {
    case none
    /// Raw DEFLATE (RFC 1951, no zlib header/trailer) matching `NSData.compressed(using: .zlib)`.
    case deflate
}

/// Control command written by the iPhone to the MCU Lab BLE GATT OTA control characteristic.
enum MCULabOTACommand: Equatable {
    case begin(size: UInt32, sha256: String, compression: MCULabOTACompression = .none)
    case beginData(size: UInt32, sha256: String, compression: MCULabOTACompression = .none)
    case commit
    case abort
}

/// Status notification sent by the MCU on the BLE GATT OTA status characteristic.
enum MCULabOTAStatus: Equatable {
    case idle
    case ready(total: UInt32, offset: UInt32 = 0)
    case progress(written: UInt32, total: UInt32)
    case ok(sha256: String)
    case error(message: String)
}

/// A single sub-phase timing span recorded on an MCU Lab board.
struct MCULabProfileSpan: Equatable, Identifiable, Decodable {
    var name: String
    var parent: String
    var startUs: UInt32
    var durationUs: UInt32
    var attrs: [String: String]? = nil

    var id: String { "\(parent).\(name).\(startUs)" }

    enum CodingKeys: String, CodingKey {
        case name, parent
        case startUs = "start_us"
        case durationUs = "dur_us"
        case attrs
    }
}

/// An application-reported custom OTel gauge metric carried inside `MCULabWakeProfile`.
struct MCULabAppMetric: Equatable, Identifiable, Decodable {
    var name: String
    var value: Int64
    var unit: String? = nil
    var attrs: [String: String]? = nil

    var id: String {
        let attrKey = (attrs ?? [:]).sorted { $0.key < $1.key }.map { "\($0.key)=\($0.value)" }.joined(separator: ",")
        return attrKey.isEmpty ? name : "\(name){\(attrKey)}"
    }

    enum CodingKeys: String, CodingKey {
        case name
        case value = "val"
        case unit
        case attrs
    }
}

/// A declarative command advertised by a firmware app inside `MCULabWakeProfile.commands`.
/// Mirrors `AppCommandSpec` in `mcu-lab/src/protocol.rs`.
struct MCULabAppCommandSpec: Equatable, Identifiable, Decodable {
    var id: String
    var label: String
    var defaultCount: UInt16

    enum CodingKeys: String, CodingKey {
        case id
        case label
        case defaultCount = "count"
    }
}

/// A sampled program-counter hotspot (`pc` hex address + sample hits).
struct MCULabPCSample: Equatable, Identifiable, Decodable {
    var pc: String
    var hits: UInt16

    var id: String { pc }
}

/// A server-symbolized PC hotspot returned by `mcu-lab-backend` (`POST /v1/traces`).
struct MCULabResolvedSymbol: Equatable, Decodable {
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

/// Hardware capability declared by a board in `mcu-lab/manifest.json`.
enum MCULabCapability: String, Hashable {
    case logicProbe = "logic-probe"
    case deepSleep = "deep-sleep"
    case epd75 = "epd75"
}

/// Physical MCU hardware board (silicon, pinout, power source, and capabilities).
enum MCULabBoard: String, CaseIterable, Identifiable {
    case xiaoESP32C3 = "xiao-esp32c3"
    case waveshareEPD75 = "waveshare-epd75"

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .xiaoESP32C3: return "XIAO ESP32-C3"
        case .waveshareEPD75: return "Waveshare EPD-75 (ESP32)"
        }
    }

    var gapName: String {
        switch self {
        case .xiaoESP32C3: return MCULabProtocol.deviceName
        case .waveshareEPD75: return "EPD-75"
        }
    }

    var chip: String {
        switch self {
        case .xiaoESP32C3: return "esp32c3"
        case .waveshareEPD75: return "esp32"
        }
    }

    /// ESP-IDF `esp_image_header_t.chip_id` (little-endian uint16 at byte offset 12).
    var chipID: UInt16 {
        switch self {
        case .xiaoESP32C3: return 0x0005
        case .waveshareEPD75: return 0x0000
        }
    }

    var boardID: UInt8 {
        switch self {
        case .xiaoESP32C3: return 1
        case .waveshareEPD75: return 2
        }
    }

    var capabilities: Set<MCULabCapability> {
        switch self {
        case .xiaoESP32C3: return [.logicProbe, .deepSleep]
        case .waveshareEPD75: return [.epd75]
        }
    }

    var compatibleApps: [MCULabApp] {
        MCULabApp.allCases.filter { $0.requiredCapabilities.isSubset(of: capabilities) }
    }
}

/// Hardware-agnostic application that runs on top of any compatible `MCULabBoard`.
enum MCULabApp: String, CaseIterable, Identifiable {
    case base = "base"
    case bench = "bench"
    case maze = "maze"
    case gzipBench = "gzip-bench"
    case grayscale = "grayscale"
    case photo = "photo"

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .base: return "Base (OTA + OTel)"
        case .bench: return "Bench (Power / EPD Sim)"
        case .maze: return "Maze Animator"
        case .gzipBench: return "Gzip Bench (OTel)"
        case .grayscale: return "Grayscale Boids"
        case .photo: return "Photo Frame"
        }
    }

    var requiredCapabilities: Set<MCULabCapability> {
        switch self {
        case .base: return []
        case .bench: return [.logicProbe]
        case .maze: return [.epd75]
        case .gzipBench: return []
        case .grayscale: return [.epd75]
        case .photo: return [.epd75]
        }
    }
}

/// Concrete flashable `(board, app)` pair published to GHCR as `<board>-<app>`.
struct MCULabFirmwareTarget: Equatable {
    var board: MCULabBoard
    var app: MCULabApp

    var binName: String { "\(board.rawValue)-\(app.rawValue)" }
    var displayName: String { "\(board.displayName) — \(app.displayName)" }
    var ghcrRepo: String { "imjasonh/playground/\(binName)" }
    var chipID: UInt16 { board.chipID }
    var boardID: UInt8 { board.boardID }
}

/// Detailed per-wake profiling snapshot pulled over BLE GATT (`PROFILE_CHAR_UUID`).
struct MCULabWakeProfile: Equatable, Decodable {
    var version: UInt8
    var wakeCount: UInt32
    var seq: UInt8
    var board: String? = nil
    var chip: String? = nil
    var app: String? = nil
    var gitSha: String? = nil
    var buildId: String? = nil
    var freeHeapBytes: UInt32
    var minFreeHeapBytes: UInt32
    var stackHighWaterBytes: UInt32
    var cpuCycles: UInt64
    var spans: [MCULabProfileSpan]
    var pcSamples: [MCULabPCSample]
    var attrs: [String: String]? = nil
    var metrics: [MCULabAppMetric]? = nil
    var commands: [MCULabAppCommandSpec]? = nil

    enum CodingKeys: String, CodingKey {
        case version = "v"
        case wakeCount = "wake"
        case seq
        case board
        case chip
        case app
        case gitSha = "git_sha"
        case buildId = "build_id"
        case freeHeapBytes = "free_heap"
        case minFreeHeapBytes = "min_heap"
        case stackHighWaterBytes = "stack_hw"
        case cpuCycles = "cycles"
        case spans
        case pcSamples = "pcs"
        case attrs
        case metrics
        case commands = "cmds"
    }
}

/// Reassembles chunked BLE GATT blob frames (`[0x4D, 0x43, index: u16 LE, total: u16 LE, payload...]`).
struct MCULabBlobReassembler {
    private var total: UInt16 = 0
    private var parts: [Data?] = []
    private var count: Int = 0

    mutating func reset() {
        total = 0
        parts.removeAll(keepingCapacity: false)
        count = 0
    }

    /// Push a raw BLE packet. Returns the reassembled payload once all frames arrive.
    mutating func push(_ raw: Data) -> Data? {
        guard raw.count >= 6,
              raw[raw.startIndex] == 0x4D,
              raw[raw.startIndex + 1] == 0x43
        else {
            return nil
        }
        let idx = raw.readUInt16LE(at: 2)
        let frameTotal = raw.readUInt16LE(at: 4)
        guard frameTotal > 0, idx < frameTotal else {
            return nil
        }
        if total != frameTotal {
            total = frameTotal
            parts = Array(repeating: nil, count: Int(frameTotal))
            count = 0
        }
        let slotIdx = Int(idx)
        if parts[slotIdx] == nil {
            parts[slotIdx] = raw.subdata(in: 6..<raw.count)
            count += 1
        }
        guard count == Int(total) else {
            return nil
        }
        var out = Data()
        for part in parts {
            if let part {
                out.append(part)
            }
        }
        reset()
        return out
    }
}

/// Shared wire format, BLE GATT OTA protocol, and OTLP JSON builder with `mcu-lab/src/protocol.rs`.
enum MCULabProtocol {
    static let deviceName = "XIAO-C3"
    static let companyID: UInt16 = 0xFFFF
    static let payloadLength = 24
    static let manufacturerDataLength = 2 + payloadLength

    static let otaServiceUUIDString = "4FAFC301-1FB5-459E-8FCC-C5C9C331914B"
    static let otaControlUUIDString = "BEB5483E-36E1-4688-B7F5-EA07361BC301"
    static let otaDataUUIDString = "BEB5483E-36E1-4688-B7F5-EA07361BC302"
    static let otaStatusUUIDString = "1A3C0001-36E1-4688-B7F5-EA07361BC303"
    static let profileCharUUIDString = "1A3C0002-36E1-4688-B7F5-EA07361BC303"
    static let coredumpCharUUIDString = "1A3C0003-36E1-4688-B7F5-EA07361BC303"
    static let appCommandCharUUIDString = "1A3C0004-36E1-4688-B7F5-EA07361BC303"
    static let maxAppCommandCount: UInt16 = 100
    static let otaSlotBytes: UInt32 = 0x1E_0000

    /// Encode a declarative app command write payload (`"<id>"` or `"<id> <count>"`).
    /// Mirrors `encode_app_command` in `mcu-lab/src/protocol.rs`.
    static func encodeAppCommand(id: String, count: UInt16) -> String {
        let normalized = id.lowercased()
        let clamped = max(1, min(count, maxAppCommandCount))
        return clamped == 1 ? normalized : "\(normalized) \(clamped)"
    }

    static let flagDeepSleepWake: UInt8 = 1 << 0
    static let flagEpdAttached: UInt8 = 1 << 1
    static let flagEpdPartial: UInt8 = 1 << 2
    static let flagBrownoutReset: UInt8 = 1 << 3

    static let otelEndpointInfoPlistKey = "MCULabOtelEndpoint"
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
    static let defaultGHCRRepo = MCULabFirmwareTarget(board: .xiaoESP32C3, app: .base).ghcrRepo
    static let defaultGitHubRepo = "imjasonh/playground"
    static let defaultFirmwarePath = "mcu-lab"
    static let defaultPublishWorkflow = "mcu-lab-publish.yml"

    /// Validate an ESP-IDF app binary header (`0xE9` magic + little-endian `chip_id` at bytes 12..14).
    /// Returns nil when valid, or an error message if the image does not match `expectedChipID`.
    static func validateESPImageHeader(_ data: Data, expectedChipID: UInt16) -> String? {
        guard data.count >= 14 else {
            return "Firmware image too small (\(data.count) B)."
        }
        guard data[data.startIndex] == 0xE9 else {
            return String(format: "Invalid ESP-IDF image magic byte 0x%02x.", data[data.startIndex])
        }
        let chipID = data.readUInt16LE(at: 12)
        guard chipID == expectedChipID else {
            return String(format: "Wrong chip_id 0x%04x (expected 0x%04x).", chipID, expectedChipID)
        }
        return nil
    }

    /// Decode a 26-byte Manufacturer Specific Data buffer (`0xFFFF` company ID + 24-byte payload).
    static func decodeManufacturerData(_ data: Data) -> MCULabMetrics? {
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
    static func encodeManufacturerData(_ metrics: MCULabMetrics) -> Data {
        var out = Data(capacity: manufacturerDataLength)
        out.appendUInt16LE(companyID)
        out.append(encodePayload(metrics))
        return out
    }

    /// Decode a 24-byte little-endian payload into `MCULabMetrics`.
    static func decodePayload(_ data: Data) -> MCULabMetrics? {
        guard data.count == payloadLength else {
            return nil
        }
        return MCULabMetrics(
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

    /// Encode `MCULabMetrics` into its 24-byte little-endian payload.
    static func encodePayload(_ metrics: MCULabMetrics) -> Data {
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

    /// Compress bytes using raw DEFLATE (RFC 1951, no zlib header/trailer),
    /// matching `OtaDeflateDecoder` in `mcu-lab/src/protocol.rs`.
    static func deflateCompress(_ data: Data) -> Data? {
        try? (data as NSData).compressed(using: .zlib) as Data
    }

    /// Encode an OTA control command matching `encode_ota_command` in `mcu-lab/src/protocol.rs`.
    static func encodeOTACommand(_ command: MCULabOTACommand) -> String {
        switch command {
        case .begin(let size, let sha256, .none):
            return "BEGIN \(size) \(sha256.lowercased())"
        case .begin(let size, let sha256, .deflate):
            return "BEGIN \(size) \(sha256.lowercased()) deflate"
        case .beginData(let size, let sha256, .none):
            return "BEGIN_DATA \(size) \(sha256.lowercased())"
        case .beginData(let size, let sha256, .deflate):
            return "BEGIN_DATA \(size) \(sha256.lowercased()) deflate"
        case .commit:
            return "COMMIT"
        case .abort:
            return "ABORT"
        }
    }

    /// Parse an OTA control command string.
    static func parseOTACommand(_ raw: String) -> MCULabOTACommand? {
        let parts = raw.split(whereSeparator: \.isWhitespace).map(String.init)
        guard let head = parts.first?.uppercased() else {
            return nil
        }
        switch head {
        case "COMMIT" where parts.count == 1:
            return .commit
        case "ABORT" where parts.count == 1:
            return .abort
        case "BEGIN", "BEGIN_DATA":
            guard parts.count == 3 || parts.count == 4 else {
                return nil
            }
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
            let compression: MCULabOTACompression
            if parts.count == 4 {
                switch parts[3].lowercased() {
                case "deflate":
                    compression = .deflate
                default:
                    return nil
                }
            } else {
                compression = .none
            }
            if head == "BEGIN_DATA" {
                return .beginData(size: size, sha256: sha, compression: compression)
            }
            return .begin(size: size, sha256: sha, compression: compression)
        default:
            return nil
        }
    }

    /// Format an OTA status line matching `format_ota_status` in `mcu-lab/src/protocol.rs`.
    static func formatOTAStatus(_ status: MCULabOTAStatus) -> String {
        switch status {
        case .idle:
            return "IDLE"
        case .ready(let total, let offset):
            return offset == 0 ? "READY total=\(total)" : "READY total=\(total) offset=\(offset)"
        case .progress(let written, let total):
            return "PROGRESS written=\(written) total=\(total)"
        case .ok(let sha256):
            return "OK sha256=\(sha256.lowercased())"
        case .error(let message):
            return "ERR \(message)"
        }
    }

    /// Parse an OTA status notification line from `OTA_STATUS_UUID`.
    static func parseOTAStatus(_ raw: String) -> MCULabOTAStatus? {
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
            var total: UInt32?
            var offset: UInt32 = 0
            for part in rest.split(whereSeparator: \.isWhitespace).map(String.init) {
                if part.hasPrefix("total=") {
                    total = UInt32(part.dropFirst("total=".count))
                } else if part.hasPrefix("offset=") {
                    offset = UInt32(part.dropFirst("offset=".count)) ?? 0
                }
            }
            guard let total else {
                return nil
            }
            return .ready(total: total, offset: offset)
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

    /// Standard IEEE 802.3 CRC32 (polynomial `0xEDB88320`) matching `mcu-lab/src/protocol.rs`.
    static func crc32(_ data: Data) -> UInt32 {
        var crc: UInt32 = 0xFFFF_FFFF
        for byte in data {
            crc ^= UInt32(byte)
            for _ in 0..<8 {
                let mask = UInt32(bitPattern: -Int32(crc & 1))
                crc = (crc >> 1) ^ (0xEDB8_8320 & mask)
            }
        }
        return ~crc
    }

    /// Encode a framed OTA data chunk (`[b'O', b'T', offset: u32 LE, crc32: u32 LE, payload...]`).
    static func encodeOTAChunkFrame(offset: UInt32, payload: Data) -> Data {
        var out = Data(capacity: 10 + payload.count)
        out.append(0x4F) // 'O'
        out.append(0x54) // 'T'
        out.appendUInt32LE(offset)
        out.appendUInt32LE(crc32(payload))
        out.append(payload)
        return out
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

    /// Split a firmware binary starting at `startOffset` into offset+CRC32 framed BLE packets.
    static func chunkFirmwareFramed(
        _ data: Data,
        startingAt startOffset: UInt32 = 0,
        maxPacketBytes: Int = 480
    ) -> [(offset: UInt32, frame: Data, payloadCount: Int)] {
        let payloadLimit = max(maxPacketBytes - 10, 20)
        let start = min(Int(startOffset), data.count)
        var out: [(offset: UInt32, frame: Data, payloadCount: Int)] = []
        var offset = start
        while offset < data.count {
            let end = min(offset + payloadLimit, data.count)
            let slice = data.subdata(in: offset..<end)
            out.append((
                offset: UInt32(offset),
                frame: encodeOTAChunkFrame(offset: UInt32(offset), payload: slice),
                payloadCount: slice.count
            ))
            offset = end
        }
        return out
    }

    /// Format a single-line summary matching `format_status_line` in `mcu-lab/src/protocol.rs`.
    static func formatStatusLine(_ m: MCULabMetrics) -> String {
        let flagsHex = String(format: "0x%02x", m.flags)
        return "seq=\(m.seq) wake=\(m.wakeCount) sensor_us=\(m.sensorUs) compute_us=\(m.computeUs) epd_us=\(m.epdRefreshUs) radio_us=\(m.radioUs) batt_mv=\(m.batteryMv) flags=\(flagsHex)"
    }

    /// Decode a `WakeProfile` JSON payload read from `PROFILE_CHAR_UUID`.
    static func decodeWakeProfile(_ data: Data) -> MCULabWakeProfile? {
        try? JSONDecoder().decode(MCULabWakeProfile.self, from: data)
    }

    /// Generate a realistic simulated `WakeProfile` for bench / Simulator testing.
    static func simulatedWakeProfile(for metrics: MCULabMetrics) -> MCULabWakeProfile {
        let bootUs: UInt32 = 420
        let sensorStart = bootUs
        let computeStart = sensorStart + metrics.sensorUs
        let epdStart = computeStart + metrics.computeUs
        let spiUs = min(metrics.epdRefreshUs / 10, 2_800)
        let busyUs = metrics.epdRefreshUs > spiUs ? metrics.epdRefreshUs - spiUs : 0
        let totalActiveUs = UInt64(bootUs) + UInt64(metrics.sensorUs) + UInt64(metrics.computeUs) + UInt64(metrics.epdRefreshUs)
        return MCULabWakeProfile(
            version: 1,
            wakeCount: metrics.wakeCount,
            seq: metrics.seq,
            freeHeapBytes: 210_944,
            minFreeHeapBytes: 198_400,
            stackHighWaterBytes: 3_072,
            cpuCycles: totalActiveUs * 160,
            spans: [
                MCULabProfileSpan(name: "boot.init", parent: "wake", startUs: 0, durationUs: bootUs),
                MCULabProfileSpan(name: "sensor.adc_filter", parent: "sensor", startUs: sensorStart, durationUs: metrics.sensorUs),
                MCULabProfileSpan(name: "compute.epd_render", parent: "compute", startUs: computeStart, durationUs: metrics.computeUs),
                MCULabProfileSpan(name: "epd.spi_transfer", parent: "epd_refresh", startUs: epdStart, durationUs: spiUs),
                MCULabProfileSpan(name: "epd.busy_wait", parent: "epd_refresh", startUs: epdStart + spiUs, durationUs: busyUs),
            ],
            pcSamples: [
                MCULabPCSample(pc: "0x42001a40", hits: 14),
                MCULabPCSample(pc: "0x42003c18", hits: 6),
                MCULabPCSample(pc: "0x42000e84", hits: 3),
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
    /// Resolve the OTLP `service.name` for a wake sample (`profile.app` when available,
    /// otherwise inferred from `metrics.boardID`).
    static func serviceName(for metrics: MCULabMetrics, profile: MCULabWakeProfile?) -> String {
        if let app = profile?.app, !app.isEmpty {
            return app
        }
        return metrics.inferredBoard.rawValue
    }

    static func formatOTLPJSON(
        deviceId: String,
        metrics: MCULabMetrics,
        rssi: Int,
        timeUnixNano: UInt64,
        profile: MCULabWakeProfile? = nil
    ) -> String {
        let ts = String(timeUnixNano)
        let safeDeviceId = escapeJSONString(deviceId)
        let safeServiceName = escapeJSONString(serviceName(for: metrics, profile: profile))
        var extraMetrics = ""
        if let profile {
            extraMetrics = """
            ,{"name":"mcu.heap.free_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.freeHeapBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.heap.min_free_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.minFreeHeapBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.stack.high_water_bytes","gauge":{"dataPoints":[{"asInt":"\(profile.stackHighWaterBytes)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.cpu.cycles","gauge":{"dataPoints":[{"asInt":"\(profile.cpuCycles)","timeUnixNano":"\(ts)"}]}}
            """
            if let appMetrics = profile.metrics, !appMetrics.isEmpty {
                var groupedOrder: [String] = []
                var groupedPoints: [String: [String]] = [:]
                for m in appMetrics {
                    let fullName = m.name.hasPrefix("mcu.app.") ? m.name : "mcu.app.\(m.name)"
                    if groupedPoints[fullName] == nil {
                        groupedOrder.append(fullName)
                        groupedPoints[fullName] = []
                    }
                    let dpAttrs = formatStringAttrs(m.attrs)
                    let dp: String
                    if dpAttrs.isEmpty {
                        dp = #"{"asInt":"\#(m.value)","timeUnixNano":"\#(ts)"}"#
                    } else {
                        dp = #"{"asInt":"\#(m.value)","timeUnixNano":"\#(ts)","attributes":[\#(dpAttrs.joined(separator: ","))]}"#
                    }
                    groupedPoints[fullName]?.append(dp)
                }
                for name in groupedOrder {
                    guard let dps = groupedPoints[name], !dps.isEmpty else { continue }
                    let safeName = escapeJSONString(name)
                    extraMetrics += #",{"name":"\#(safeName)","gauge":{"dataPoints":[\#(dps.joined(separator: ","))]}}"#
                }
            }
        }
        return """
        {"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"\(safeServiceName)"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeMetrics":[{"metrics":[{"name":"mcu.wake.count","gauge":{"dataPoints":[{"asInt":"\(metrics.wakeCount)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.phase.duration_us","gauge":{"dataPoints":[{"asInt":"\(metrics.sensorUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"sensor"}}]},{"asInt":"\(metrics.computeUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"compute"}}]},{"asInt":"\(metrics.epdRefreshUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"epd_refresh"}}]},{"asInt":"\(metrics.radioUs)","timeUnixNano":"\(ts)","attributes":[{"key":"phase","value":{"stringValue":"radio"}}]}]}},{"name":"mcu.battery_mv","gauge":{"dataPoints":[{"asInt":"\(metrics.batteryMv)","timeUnixNano":"\(ts)"}]}},{"name":"mcu.ble.rssi","gauge":{"dataPoints":[{"asInt":"\(rssi)","timeUnixNano":"\(ts)"}]}}\(extraMetrics)]}]}]}
        """
    }

    private static func formatStringAttrs(_ attrs: [String: String]?) -> [String] {
        guard let attrs, !attrs.isEmpty else { return [] }
        return attrs.keys.sorted().compactMap { key in
            guard let val = attrs[key], !key.isEmpty else { return nil }
            return #"{"key":"\#(escapeJSONString(key))","value":{"stringValue":"\#(escapeJSONString(val))"}}"#
        }
    }

    /// Build a valid OTLP/HTTP v1 JSON trace payload (`ExportTraceServiceRequest`) representing
    /// the wake waterfall (`xiao.wake` root span + 4 MCU phase spans + optional firmware sub-phase spans).
    static func formatOTLPTraceJSON(
        traceId: String,
        rootSpanId: String,
        deviceId: String,
        metrics: MCULabMetrics,
        rssi: Int,
        timeUnixNano: UInt64,
        profile: MCULabWakeProfile? = nil
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
            if let board = profile.board, !board.isEmpty {
                rootAttrs.append(#"{"key":"mcu.board","value":{"stringValue":"\#(escapeJSONString(board))"}}"#)
            }
            if let chip = profile.chip, !chip.isEmpty {
                rootAttrs.append(#"{"key":"mcu.chip","value":{"stringValue":"\#(escapeJSONString(chip))"}}"#)
            }
            if let app = profile.app, !app.isEmpty {
                rootAttrs.append(#"{"key":"mcu.app","value":{"stringValue":"\#(escapeJSONString(app))"}}"#)
            }
            if let gitSha = profile.gitSha, !gitSha.isEmpty {
                rootAttrs.append(#"{"key":"mcu.git_sha","value":{"stringValue":"\#(escapeJSONString(gitSha))"}}"#)
            }
            if let buildId = profile.buildId, !buildId.isEmpty {
                rootAttrs.append(#"{"key":"mcu.build_id","value":{"stringValue":"\#(escapeJSONString(buildId))"}}"#)
            }
            rootAttrs.append(#"{"key":"mcu.heap.free_bytes","value":{"intValue":"\#(profile.freeHeapBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.heap.min_free_bytes","value":{"intValue":"\#(profile.minFreeHeapBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.stack.high_water_bytes","value":{"intValue":"\#(profile.stackHighWaterBytes)"}}"#)
            rootAttrs.append(#"{"key":"mcu.cpu.cycles","value":{"intValue":"\#(profile.cpuCycles)"}}"#)
            rootAttrs.append(contentsOf: formatStringAttrs(profile.attrs))
            for sample in profile.pcSamples {
                let safePc = escapeJSONString(sample.pc)
                rootEvents.append(
                    #"{"timeUnixNano":"\#(wakeEndNs)","name":"pc.hotspot","attributes":[{"key":"pc","value":{"stringValue":"\#(safePc)"}},{"key":"hits","value":{"intValue":"\#(sample.hits)"}}]}"#
                )
            }
        }

        let resolvedService = serviceName(for: metrics, profile: profile)
        let rootSpanName = resolvedService == MCULabBoard.xiaoESP32C3.rawValue
            ? "xiao.wake #\(metrics.wakeCount)"
            : "\(resolvedService).wake #\(metrics.wakeCount)"

        var spans: [String] = [
            formatSpanJSON(
                traceId: traceId,
                spanId: rootSpanId,
                parentSpanId: nil,
                name: rootSpanName,
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
                        endNs: subEnd,
                        attrs: formatStringAttrs(sub.attrs)
                    )
                )
            }
        }

        let safeDeviceId = escapeJSONString(deviceId)
        let safeServiceName = escapeJSONString(resolvedService)
        return """
        {"resourceSpans":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"\(safeServiceName)"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeSpans":[{"spans":[\(spans.joined(separator: ","))]}]}]}
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

    /// Build an OTLP/HTTP v1 JSON metrics payload for a completed (or failed) BLE OTA update.
    static func formatOTAOTLPMetricsJSON(
        deviceId: String,
        report: MCULabOTAReport,
        timeUnixNano: UInt64
    ) -> String {
        let ts = String(timeUnixNano)
        let safeDeviceId = escapeJSONString(deviceId)
        let safeService = escapeJSONString(report.board.rawValue)
        let safeApp = escapeJSONString(report.app.rawValue)
        let safeCompression = escapeJSONString(report.compression.rawValue)
        let safeOutcome = escapeJSONString(report.isSuccess ? "ok" : "error")
        let commonAttrs = """
        {"key":"app","value":{"stringValue":"\(safeApp)"}},\
        {"key":"compression","value":{"stringValue":"\(safeCompression)"}},\
        {"key":"outcome","value":{"stringValue":"\(safeOutcome)"}}
        """

        func phasePoint(_ phase: String, _ ms: Int) -> String {
            #"{"asInt":"\#(ms)","timeUnixNano":"\#(ts)","attributes":[{"key":"phase","value":{"stringValue":"\#(phase)"}},\#(commonAttrs)]}"#
        }

        var metrics: [String] = [
            """
            {"name":"mcu.ota.duration_ms","gauge":{"dataPoints":[\
            \(phasePoint("total", report.totalMs)),\
            \(phasePoint("connect", report.connectMs)),\
            \(phasePoint("erase", report.eraseMs)),\
            \(phasePoint("stream", report.streamMs)),\
            \(phasePoint("commit", report.commitMs))\
            ]}}
            """,
            """
            {"name":"mcu.ota.throughput_bps","gauge":{"dataPoints":[\
            {"asInt":"\(report.effectiveBytesPerSec)","timeUnixNano":"\(ts)","attributes":[{"key":"kind","value":{"stringValue":"effective"}},\(commonAttrs)]},\
            {"asInt":"\(report.wireBytesPerSec)","timeUnixNano":"\(ts)","attributes":[{"key":"kind","value":{"stringValue":"wire"}},\(commonAttrs)]}\
            ]}}
            """,
            """
            {"name":"mcu.ota.bytes","gauge":{"dataPoints":[\
            {"asInt":"\(report.rawBytes)","timeUnixNano":"\(ts)","attributes":[{"key":"kind","value":{"stringValue":"raw"}},\(commonAttrs)]},\
            {"asInt":"\(report.wireBytes)","timeUnixNano":"\(ts)","attributes":[{"key":"kind","value":{"stringValue":"wire"}},\(commonAttrs)]}\
            ]}}
            """,
            """
            {"name":"mcu.ota.rtt_ms","gauge":{"dataPoints":[\
            {"asInt":"\(Int(report.avgRttMs.rounded()))","timeUnixNano":"\(ts)","attributes":[\(commonAttrs)]}\
            ]}}
            """,
            """
            {"name":"mcu.ota.energy_mj","gauge":{"dataPoints":[\
            {"asInt":"\(report.estimatedMcuEnergyMj)","timeUnixNano":"\(ts)","attributes":[\(commonAttrs)]}\
            ]}}
            """,
        ]

        if let deltaMv = report.mcuBatteryDeltaMv {
            metrics.append(
                """
                {"name":"mcu.ota.battery_delta_mv","gauge":{"dataPoints":[\
                {"asInt":"\(deltaMv)","timeUnixNano":"\(ts)","attributes":[\(commonAttrs)]}\
                ]}}
                """
            )
        }
        if let phoneDelta = report.phoneBatteryDeltaPct {
            metrics.append(
                """
                {"name":"mcu.ota.phone_battery_pct","gauge":{"dataPoints":[\
                {"asInt":"\(phoneDelta)","timeUnixNano":"\(ts)","attributes":[\(commonAttrs)]}\
                ]}}
                """
            )
        }

        return """
        {"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"\(safeService)"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeMetrics":[{"metrics":[\(metrics.joined(separator: ","))]}]}]}
        """
    }

    /// Build an OTLP/HTTP v1 JSON trace payload for a BLE OTA update with connect/erase/stream/commit child spans.
    static func formatOTAOTLPTraceJSON(
        traceId: String,
        rootSpanId: String,
        deviceId: String,
        report: MCULabOTAReport
    ) -> String {
        let startNs = UInt64(max(0, report.startedAt.timeIntervalSince1970) * 1_000_000_000)
        let connectEnd = startNs + UInt64(max(0, report.connectMs)) * 1_000_000
        let eraseEnd = connectEnd + UInt64(max(0, report.eraseMs)) * 1_000_000
        let streamEnd = eraseEnd + UInt64(max(0, report.streamMs)) * 1_000_000
        let commitEnd = streamEnd + UInt64(max(0, report.commitMs)) * 1_000_000
        let totalEnd = max(commitEnd, startNs + UInt64(max(1, report.totalMs)) * 1_000_000)

        var rootAttrs: [String] = [
            #"{"key":"ota.board","value":{"stringValue":"\#(escapeJSONString(report.board.rawValue))"}}"#,
            #"{"key":"ota.app","value":{"stringValue":"\#(escapeJSONString(report.app.rawValue))"}}"#,
            #"{"key":"ota.image","value":{"stringValue":"\#(escapeJSONString(report.imageName))"}}"#,
            #"{"key":"ota.sha256","value":{"stringValue":"\#(escapeJSONString(report.sha256))"}}"#,
            #"{"key":"ota.compression","value":{"stringValue":"\#(escapeJSONString(report.compression.rawValue))"}}"#,
            #"{"key":"ota.outcome","value":{"stringValue":"\#(escapeJSONString(report.outcome))"}}"#,
            #"{"key":"ota.raw_bytes","value":{"intValue":"\#(report.rawBytes)"}}"#,
            #"{"key":"ota.wire_bytes","value":{"intValue":"\#(report.wireBytes)"}}"#,
            #"{"key":"ota.packets","value":{"intValue":"\#(report.packetCount)"}}"#,
            #"{"key":"ota.chunk_bytes","value":{"intValue":"\#(report.chunkSize)"}}"#,
            #"{"key":"ota.effective_bps","value":{"intValue":"\#(report.effectiveBytesPerSec)"}}"#,
            #"{"key":"ota.wire_bps","value":{"intValue":"\#(report.wireBytesPerSec)"}}"#,
            #"{"key":"ota.avg_rtt_ms","value":{"intValue":"\#(Int(report.avgRttMs.rounded()))"}}"#,
            #"{"key":"ota.mcu_energy_mj","value":{"intValue":"\#(report.estimatedMcuEnergyMj)"}}"#,
        ]
        if let startMv = report.mcuBatteryStartMv {
            rootAttrs.append(#"{"key":"ota.mcu_battery_start_mv","value":{"intValue":"\#(startMv)"}}"#)
        }
        if let endMv = report.mcuBatteryEndMv {
            rootAttrs.append(#"{"key":"ota.mcu_battery_end_mv","value":{"intValue":"\#(endMv)"}}"#)
        }
        if let startPct = report.phoneBatteryStartPct {
            rootAttrs.append(#"{"key":"ota.phone_battery_start_pct","value":{"intValue":"\#(startPct)"}}"#)
        }
        if let endPct = report.phoneBatteryEndPct {
            rootAttrs.append(#"{"key":"ota.phone_battery_end_pct","value":{"intValue":"\#(endPct)"}}"#)
        }

        let spans: [String] = [
            formatSpanJSON(
                traceId: traceId,
                spanId: rootSpanId,
                parentSpanId: nil,
                name: "ota.update \(report.board.rawValue)-\(report.app.rawValue)",
                startNs: startNs,
                endNs: totalEnd,
                attrs: rootAttrs
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: randomHex(byteCount: 8),
                parentSpanId: rootSpanId,
                name: "ota.connect",
                startNs: startNs,
                endNs: connectEnd
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: randomHex(byteCount: 8),
                parentSpanId: rootSpanId,
                name: "ota.erase",
                startNs: connectEnd,
                endNs: eraseEnd
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: randomHex(byteCount: 8),
                parentSpanId: rootSpanId,
                name: "ota.stream",
                startNs: eraseEnd,
                endNs: streamEnd
            ),
            formatSpanJSON(
                traceId: traceId,
                spanId: randomHex(byteCount: 8),
                parentSpanId: rootSpanId,
                name: "ota.commit",
                startNs: streamEnd,
                endNs: commitEnd
            ),
        ]

        let safeDeviceId = escapeJSONString(deviceId)
        let safeService = escapeJSONString(report.board.rawValue)
        return """
        {"resourceSpans":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"\(safeService)"}},{"key":"device.id","value":{"stringValue":"\(safeDeviceId)"}}]},"scopeSpans":[{"spans":[\(spans.joined(separator: ","))]}]}]}
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

/// Performance and battery-drain telemetry recorded for a single BLE OTA update.
struct MCULabOTAReport: Equatable {
    var board: MCULabBoard
    var app: MCULabApp
    var imageName: String
    var sha256: String
    var compression: MCULabOTACompression
    var outcome: String
    var rawBytes: Int
    var wireBytes: Int
    var packetCount: Int
    var chunkSize: Int
    var startedAt: Date
    var completedAt: Date
    var connectMs: Int
    var eraseMs: Int
    var streamMs: Int
    var commitMs: Int
    var totalMs: Int
    var mcuBatteryStartMv: UInt16?
    var mcuBatteryEndMv: UInt16?
    var phoneBatteryStartPct: Int?
    var phoneBatteryEndPct: Int?

    var isSuccess: Bool {
        outcome == "ok"
    }

    /// Effective flashing speed in uncompressed bytes/sec during the streaming phase.
    var effectiveBytesPerSec: Int {
        guard streamMs > 0 else { return 0 }
        return Int((Double(rawBytes) / (Double(streamMs) / 1_000.0)).rounded())
    }

    /// Wire throughput in BLE bytes/sec during the streaming phase.
    var wireBytesPerSec: Int {
        guard streamMs > 0 else { return 0 }
        return Int((Double(wireBytes) / (Double(streamMs) / 1_000.0)).rounded())
    }

    /// Average per-packet round-trip time (ms) for ACKed `.withResponse` writes.
    var avgRttMs: Double {
        guard packetCount > 0 else { return 0 }
        return Double(streamMs) / Double(packetCount)
    }

    /// Percentage of wire bytes saved by compression (`0` when uncompressed).
    var compressionSavedPct: Int {
        guard rawBytes > 0, wireBytes < rawBytes else { return 0 }
        return Int(((1.0 - Double(wireBytes) / Double(rawBytes)) * 100.0).rounded())
    }

    /// Estimated MCU energy consumed during OTA in millijoules (~95 mA average BLE RX + flash write).
    var estimatedMcuEnergyMj: Int {
        let vMv = Int64((mcuBatteryStartMv ?? 0) > 0 ? (mcuBatteryStartMv ?? 3700) : 3700)
        // P(mW) = V(mV) * I(mA) / 1000; E(mJ) = P(mW) * t(s) = V(mV) * I(mA) * t(ms) / 1_000_000.
        return Int((Int64(max(0, totalMs)) * 95 * vMv) / 1_000_000)
    }

    /// Measured MCU battery voltage change (mV) from pre-OTA wake to first post-reboot wake.
    var mcuBatteryDeltaMv: Int? {
        guard let start = mcuBatteryStartMv, let end = mcuBatteryEndMv, start > 0, end > 0 else {
            return nil
        }
        return Int(end) - Int(start)
    }

    /// Measured iPhone battery percentage change during the OTA transfer.
    var phoneBatteryDeltaPct: Int? {
        guard let start = phoneBatteryStartPct, let end = phoneBatteryEndPct else {
            return nil
        }
        return end - start
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

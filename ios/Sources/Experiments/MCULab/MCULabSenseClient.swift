import Foundation

/// Source of an on-device tag detected on the XIAO ESP32-S3 Sense.
enum MCULabSenseTagSource: String, Codable, Equatable, Sendable {
    case audio
    case vision
    case model

    var systemImage: String {
        switch self {
        case .audio: return "waveform"
        case .vision: return "eye"
        case .model: return "cpu"
        }
    }
}

/// A single on-device tag attached to a recorded clip (`clip_NNNNNN.json` sidecar).
struct MCULabSenseTag: Codable, Equatable, Identifiable, Sendable {
    var label: String
    var source: MCULabSenseTagSource
    var confidence: UInt8
    var firstS: UInt32
    var count: UInt32

    var id: String { "\(source.rawValue):\(label)" }

    enum CodingKeys: String, CodingKey {
        case label
        case source
        case confidence
        case firstS = "first_s"
        case count
    }
}

/// Aggregate tag count returned by `GET /api/tags` or computed across clips.
struct MCULabSenseTagCount: Codable, Equatable, Identifiable, Sendable {
    var label: String
    var count: Int

    var id: String { label }
}

/// Response payload returned by `GET /api/tags`.
struct MCULabSenseTagsResponse: Codable, Equatable, Sendable {
    var tags: [MCULabSenseTagCount]
}

/// Runtime status payload returned by `GET /api/status` on the XIAO ESP32-S3 Sense recorder.
struct MCULabSenseStatus: Codable, Equatable, Sendable {
    var board: String
    var app: String
    var firmwareId: String
    var recording: Bool
    var clipDurationS: UInt32
    var clipCount: Int
    var activeClip: String?
    var sdMounted: Bool
    var sdTotalBytes: UInt64
    var sdFreeBytes: UInt64
    var wifiMode: String
    var ssid: String
    var ip: String
    var cameraReady: Bool
    var micReady: Bool
    var models: [String]
    var activeTags: [String]

    enum CodingKeys: String, CodingKey {
        case board
        case app
        case firmwareId = "firmware_id"
        case recording
        case clipDurationS = "clip_duration_s"
        case clipCount = "clip_count"
        case activeClip = "active_clip"
        case sdMounted = "sd_mounted"
        case sdTotalBytes = "sd_total_bytes"
        case sdFreeBytes = "sd_free_bytes"
        case wifiMode = "wifi_mode"
        case ssid
        case ip
        case cameraReady = "camera_ready"
        case micReady = "mic_ready"
        case models
        case activeTags = "active_tags"
    }

    init(
        board: String,
        app: String,
        firmwareId: String,
        recording: Bool,
        clipDurationS: UInt32,
        clipCount: Int,
        activeClip: String?,
        sdMounted: Bool,
        sdTotalBytes: UInt64,
        sdFreeBytes: UInt64,
        wifiMode: String,
        ssid: String,
        ip: String,
        cameraReady: Bool,
        micReady: Bool,
        models: [String] = [],
        activeTags: [String] = []
    ) {
        self.board = board
        self.app = app
        self.firmwareId = firmwareId
        self.recording = recording
        self.clipDurationS = clipDurationS
        self.clipCount = clipCount
        self.activeClip = activeClip
        self.sdMounted = sdMounted
        self.sdTotalBytes = sdTotalBytes
        self.sdFreeBytes = sdFreeBytes
        self.wifiMode = wifiMode
        self.ssid = ssid
        self.ip = ip
        self.cameraReady = cameraReady
        self.micReady = micReady
        self.models = models
        self.activeTags = activeTags
    }

    init(from decoder: Decoder) throws {
        let c = try decoder.container(keyedBy: CodingKeys.self)
        board = try c.decode(String.self, forKey: .board)
        app = try c.decode(String.self, forKey: .app)
        firmwareId = try c.decode(String.self, forKey: .firmwareId)
        recording = try c.decode(Bool.self, forKey: .recording)
        clipDurationS = try c.decode(UInt32.self, forKey: .clipDurationS)
        clipCount = try c.decode(Int.self, forKey: .clipCount)
        activeClip = try c.decodeIfPresent(String.self, forKey: .activeClip)
        sdMounted = try c.decode(Bool.self, forKey: .sdMounted)
        sdTotalBytes = try c.decode(UInt64.self, forKey: .sdTotalBytes)
        sdFreeBytes = try c.decode(UInt64.self, forKey: .sdFreeBytes)
        wifiMode = try c.decode(String.self, forKey: .wifiMode)
        ssid = try c.decode(String.self, forKey: .ssid)
        ip = try c.decode(String.self, forKey: .ip)
        cameraReady = try c.decode(Bool.self, forKey: .cameraReady)
        micReady = try c.decode(Bool.self, forKey: .micReady)
        models = try c.decodeIfPresent([String].self, forKey: .models) ?? []
        activeTags = try c.decodeIfPresent([String].self, forKey: .activeTags) ?? []
    }
}

/// Metadata for a single finalized `.mov` clip stored on the Sense's microSD card.
struct MCULabSenseClip: Codable, Equatable, Identifiable, Sendable {
    var name: String
    var seq: UInt32
    var sizeBytes: UInt64
    var durationS: UInt32
    var tags: [MCULabSenseTag]

    var id: String { name }

    enum CodingKeys: String, CodingKey {
        case name
        case seq
        case sizeBytes = "size_bytes"
        case durationS = "duration_s"
        case tags
    }

    init(
        name: String,
        seq: UInt32,
        sizeBytes: UInt64,
        durationS: UInt32,
        tags: [MCULabSenseTag] = []
    ) {
        self.name = name
        self.seq = seq
        self.sizeBytes = sizeBytes
        self.durationS = durationS
        self.tags = tags
    }

    init(from decoder: Decoder) throws {
        let c = try decoder.container(keyedBy: CodingKeys.self)
        name = try c.decode(String.self, forKey: .name)
        seq = try c.decode(UInt32.self, forKey: .seq)
        sizeBytes = try c.decode(UInt64.self, forKey: .sizeBytes)
        durationS = try c.decode(UInt32.self, forKey: .durationS)
        tags = try c.decodeIfPresent([MCULabSenseTag].self, forKey: .tags) ?? []
    }
}

/// Response payload returned by `GET /api/clips` on the XIAO ESP32-S3 Sense recorder.
struct MCULabSenseClipsResponse: Codable, Equatable, Sendable {
    var clips: [MCULabSenseClip]
    var sdTotalBytes: UInt64
    var sdFreeBytes: UInt64
    var recording: Bool

    enum CodingKeys: String, CodingKey {
        case clips
        case sdTotalBytes = "sd_total_bytes"
        case sdFreeBytes = "sd_free_bytes"
        case recording
    }
}

/// Pure helpers for computing tag filter chips and filtering clips by tag label.
enum MCULabSenseTagFilter {
    static func tagCounts(in clips: [MCULabSenseClip]) -> [MCULabSenseTagCount] {
        var counts: [String: Int] = [:]
        for clip in clips {
            let uniqueLabels = Set(clip.tags.map { $0.label.lowercased() })
            for label in uniqueLabels {
                counts[label, default: 0] += 1
            }
        }
        return counts
            .map { MCULabSenseTagCount(label: $0.key, count: $0.value) }
            .sorted { lhs, rhs in
                if lhs.count != rhs.count { return lhs.count > rhs.count }
                return lhs.label < rhs.label
            }
    }

    static func filter(_ clips: [MCULabSenseClip], by tag: String?) -> [MCULabSenseClip] {
        guard let wanted = tag?.trimmingCharacters(in: .whitespacesAndNewlines),
              !wanted.isEmpty
        else {
            return clips
        }
        return clips.filter { clip in
            clip.tags.contains { $0.label.caseInsensitiveCompare(wanted) == .orderedSame }
        }
    }
}

/// Normalizes user-entered Sense HTTP server addresses (`192.168.4.1`, `http://192.168.1.42/`).
enum MCULabSenseServerAddress {
    static let defaultAddress = "http://192.168.4.1"

    static func normalize(_ raw: String) -> URL? {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }
        let withScheme: String
        if trimmed.contains("://") {
            withScheme = trimmed
        } else {
            withScheme = "http://\(trimmed)"
        }
        guard var components = URLComponents(string: withScheme),
              let scheme = components.scheme?.lowercased(),
              scheme == "http" || scheme == "https",
              let host = components.host,
              !host.isEmpty
        else {
            return nil
        }
        // Strip any trailing slash so endpoints concatenate cleanly.
        while components.path.hasSuffix("/") {
            components.path.removeLast()
        }
        components.query = nil
        components.fragment = nil
        return components.url
    }
}

/// Human-readable formatting helpers for SD card storage and clip durations.
enum MCULabSenseFormatting {
    static func formatBytes(_ bytes: UInt64) -> String {
        let kb = 1_024.0
        let mb = kb * 1_024.0
        let gb = mb * 1_024.0
        let value = Double(bytes)
        if value >= gb {
            return String(format: "%.1f GB", value / gb)
        } else if value >= mb {
            return String(format: "%.1f MB", value / mb)
        } else if value >= kb {
            return String(format: "%.0f KB", value / kb)
        } else {
            return "\(bytes) B"
        }
    }

    static func formatDuration(_ seconds: UInt32) -> String {
        let mins = seconds / 60
        let secs = seconds % 60
        return String(format: "%d:%02d", mins, secs)
    }
}

enum MCULabSenseClientError: LocalizedError, Equatable {
    case invalidAddress
    case httpStatus(Int)
    case invalidResponse

    var errorDescription: String? {
        switch self {
        case .invalidAddress:
            return "Enter a valid HTTP address (for example 192.168.4.1)."
        case .httpStatus(let code):
            return "Sense server returned HTTP \(code)."
        case .invalidResponse:
            return "Unexpected response from Sense server."
        }
    }
}

/// Minimal async HTTP transport protocol so `MCULabSenseClient` can be unit-tested without network I/O.
protocol MCULabSenseHTTPClient: Sendable {
    func data(for request: URLRequest) async throws -> (Data, URLResponse)
}

extension URLSession: MCULabSenseHTTPClient {}

/// Async HTTP client for browsing, streaming, filtering, and controlling a XIAO ESP32-S3 Sense recorder.
struct MCULabSenseClient: Sendable {
    let baseURL: URL
    private let http: any MCULabSenseHTTPClient

    init(baseURL: URL, http: any MCULabSenseHTTPClient = URLSession.shared) {
        self.baseURL = baseURL
        self.http = http
    }

    func fetchStatus() async throws -> MCULabSenseStatus {
        let url = baseURL.appendingPathComponent("api/status")
        return try await getJSON(MCULabSenseStatus.self, from: url)
    }

    func fetchClips(tag: String? = nil) async throws -> MCULabSenseClipsResponse {
        var url = baseURL.appendingPathComponent("api/clips")
        if let tag = tag?.trimmingCharacters(in: .whitespacesAndNewlines),
           !tag.isEmpty,
           var components = URLComponents(url: url, resolvingAgainstBaseURL: false)
        {
            components.queryItems = [URLQueryItem(name: "tag", value: tag)]
            if let filteredURL = components.url {
                url = filteredURL
            }
        }
        return try await getJSON(MCULabSenseClipsResponse.self, from: url)
    }

    func fetchTags() async throws -> MCULabSenseTagsResponse {
        let url = baseURL.appendingPathComponent("api/tags")
        return try await getJSON(MCULabSenseTagsResponse.self, from: url)
    }

    func setRecording(_ enabled: Bool) async throws -> MCULabSenseStatus {
        let path = enabled ? "api/record/start" : "api/record/stop"
        var req = URLRequest(url: baseURL.appendingPathComponent(path))
        req.httpMethod = "POST"
        req.timeoutInterval = 8
        let (data, response) = try await http.data(for: req)
        try validateHTTP(response)
        return try JSONDecoder().decode(MCULabSenseStatus.self, from: data)
    }

    func deleteClip(_ clip: MCULabSenseClip) async throws {
        var req = URLRequest(url: baseURL.appendingPathComponent("api/clips/\(clip.name)"))
        req.httpMethod = "DELETE"
        req.timeoutInterval = 8
        let (_, response) = try await http.data(for: req)
        try validateHTTP(response)
    }

    func clipStreamURL(for clip: MCULabSenseClip) -> URL {
        baseURL.appendingPathComponent("clips/\(clip.name)")
    }

    private func getJSON<T: Decodable>(_ type: T.Type, from url: URL) async throws -> T {
        var req = URLRequest(url: url)
        req.httpMethod = "GET"
        req.timeoutInterval = 8
        req.cachePolicy = .reloadIgnoringLocalCacheData
        let (data, response) = try await http.data(for: req)
        try validateHTTP(response)
        return try JSONDecoder().decode(T.self, from: data)
    }

    private func validateHTTP(_ response: URLResponse) throws {
        guard let http = response as? HTTPURLResponse else {
            throw MCULabSenseClientError.invalidResponse
        }
        guard (200..<300).contains(http.statusCode) else {
            throw MCULabSenseClientError.httpStatus(http.statusCode)
        }
    }
}

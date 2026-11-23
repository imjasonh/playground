import Foundation

/// Per-network persisted baseline so home LAN state stays isolated from public Wi-Fi.
struct NetworkBaseline: Codable, Equatable, Sendable {
    var networkID: String
    var displayName: String
    var trust: NetworkTrust
    var firstSeen: Date
    var lastSeen: Date
    var gatewayIP: String?
    var gatewayMAC: String?
    var dnsServers: [String]
    var proxyEnabled: Bool
    /// Known devices keyed by normalized MAC (or IP fallback).
    var knownDevices: [String: LANDevice]
    /// Known UPnP port forward IDs.
    var knownUPnPMappings: [String: UPnPMapping]
    /// Trusted wildcard listening ports on this Mac (e.g. "AirPlayXPCHelper:7000").
    var trustedListeners: Set<String>
    /// Trusted high-fan-out processes on this Mac (e.g. "Tailscale", "Transmission").
    var trustedProcesses: Set<String>

    init(
        networkID: String,
        displayName: String,
        trust: NetworkTrust = .unknown,
        now: Date = Date()
    ) {
        self.networkID = networkID
        self.displayName = displayName
        self.trust = trust
        self.firstSeen = now
        self.lastSeen = now
        self.gatewayIP = nil
        self.gatewayMAC = nil
        self.dnsServers = []
        self.proxyEnabled = false
        self.knownDevices = [:]
        self.knownUPnPMappings = [:]
        self.trustedListeners = []
        self.trustedProcesses = []
    }
}

/// Optional configuration for external DNS / router vantage points (Phase 4).
struct ExternalVantageConfig: Codable, Equatable, Sendable {
    enum Provider: String, Codable, Equatable, Sendable, CaseIterable {
        case none
        case pihole
        case adguardHome

        var label: String {
            switch self {
            case .none: return "Disabled"
            case .pihole: return "Pi-hole"
            case .adguardHome: return "AdGuard Home"
            }
        }
    }

    var provider: Provider = .none
    var baseURL: String = ""
    var apiToken: String = ""
    /// Alert if a single LAN client sends more than this many DNS queries in the summary window.
    var chattyQueryThreshold: Int = 5_000
}

/// Root persisted state for Lantern.
struct LanternState: Codable, Equatable, Sendable {
    var baselines: [String: NetworkBaseline] = [:]
    var findings: [Finding] = []
    var muteRules: [MuteRule] = []
    /// Cooldown timestamps keyed by dedupeKey so alerts don't re-notify constantly.
    var lastNotifiedByKey: [String: Date] = [:]
    var scanIntervalSeconds: Int = 60
    var notificationsEnabled: Bool = true
    var externalVantage: ExternalVantageConfig = ExternalVantageConfig()
}

/// JSON-backed store in `~/Library/Application Support/Lantern/state.json` (or a custom URL for tests).
final class BaselineStore: @unchecked Sendable {
    private let fileURL: URL
    private let lock = NSLock()
    private var cachedState: LanternState

    init(fileURL: URL? = nil) {
        if let fileURL {
            self.fileURL = fileURL
        } else {
            let appSupport = FileManager.default.urls(
                for: .applicationSupportDirectory,
                in: .userDomainMask
            ).first ?? URL(fileURLWithPath: NSTemporaryDirectory())
            self.fileURL = appSupport
                .appendingPathComponent("Lantern", isDirectory: true)
                .appendingPathComponent("state.json")
        }
        self.cachedState = Self.loadFromDisk(url: self.fileURL) ?? LanternState()
    }

    var state: LanternState {
        lock.lock()
        defer { lock.unlock() }
        return cachedState
    }

    @discardableResult
    func update<T>(_ mutate: (inout LanternState) -> T) -> T {
        lock.lock()
        let result = mutate(&cachedState)
        let snapshot = cachedState
        lock.unlock()
        saveToDisk(snapshot)
        return result
    }

    func baseline(for network: NetworkIdentity, now: Date = Date()) -> NetworkBaseline {
        update { state in
            if var existing = state.baselines[network.id] {
                existing.lastSeen = now
                if !network.displayName.isEmpty, network.displayName != "Offline" {
                    existing.displayName = network.displayName
                }
                state.baselines[network.id] = existing
                return existing
            }
            let created = NetworkBaseline(
                networkID: network.id,
                displayName: network.displayName,
                trust: .unknown,
                now: now
            )
            state.baselines[network.id] = created
            return created
        }
    }

    func setTrust(_ trust: NetworkTrust, for networkID: String) {
        update { state in
            if var baseline = state.baselines[networkID] {
                baseline.trust = trust
                state.baselines[networkID] = baseline
            }
        }
    }

    func trustDevice(mac: String, networkID: String, trusted: Bool = true) {
        update { state in
            guard var baseline = state.baselines[networkID],
                  var device = baseline.knownDevices[mac]
            else { return }
            device.isTrusted = trusted
            baseline.knownDevices[mac] = device
            state.baselines[networkID] = baseline
        }
    }

    func setDeviceClassification(
        _ classification: DeviceClassification,
        mac: String,
        networkID: String
    ) {
        update { state in
            guard var baseline = state.baselines[networkID],
                  var device = baseline.knownDevices[mac]
            else { return }
            device.classification = classification
            baseline.knownDevices[mac] = device
            state.baselines[networkID] = baseline
        }
    }

    func trustProcess(_ processName: String, networkID: String) {
        update { state in
            guard var baseline = state.baselines[networkID] else { return }
            baseline.trustedProcesses.insert(processName)
            state.baselines[networkID] = baseline
        }
    }

    func mute(finding: Finding) {
        update { state in
            let rule = MuteRule(
                networkID: finding.networkID,
                dedupeKey: finding.dedupeKey,
                label: finding.title
            )
            if !state.muteRules.contains(where: {
                $0.networkID == rule.networkID && $0.dedupeKey == rule.dedupeKey
            }) {
                state.muteRules.append(rule)
            }
            state.findings.removeAll {
                $0.networkID == finding.networkID && $0.dedupeKey == finding.dedupeKey
            }
        }
    }

    func removeMuteRule(id: UUID) {
        update { state in
            state.muteRules.removeAll { $0.id == id }
        }
    }

    func isMuted(networkID: String, dedupeKey: String) -> Bool {
        let current = state
        return current.muteRules.contains {
            $0.networkID == networkID && $0.dedupeKey == dedupeKey
        }
    }

    private static func loadFromDisk(url: URL) -> LanternState? {
        guard let data = try? Data(contentsOf: url) else { return nil }
        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601
        return try? decoder.decode(LanternState.self, from: data)
    }

    private func saveToDisk(_ snapshot: LanternState) {
        do {
            let dir = fileURL.deletingLastPathComponent()
            try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
            let encoder = JSONEncoder()
            encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
            encoder.dateEncodingStrategy = .iso8601
            let data = try encoder.encode(snapshot)
            try data.write(to: fileURL, options: .atomic)
        } catch {
            // Persistence failure is non-fatal; state remains in memory.
        }
    }
}

import Foundation

/// Severity levels for deterministic findings emitted by Lantern.
enum FindingSeverity: String, Codable, Equatable, Comparable, Sendable, CaseIterable {
    case info
    case notice
    case warning
    case critical

    private var rank: Int {
        switch self {
        case .info: return 0
        case .notice: return 1
        case .warning: return 2
        case .critical: return 3
        }
    }

    static func < (lhs: FindingSeverity, rhs: FindingSeverity) -> Bool {
        lhs.rank < rhs.rank
    }

    var label: String {
        switch self {
        case .info: return "Info"
        case .notice: return "Notice"
        case .warning: return "Warning"
        case .critical: return "Critical"
        }
    }

    var symbolName: String {
        switch self {
        case .info: return "info.circle.fill"
        case .notice: return "bell.badge.fill"
        case .warning: return "exclamationmark.triangle.fill"
        case .critical: return "shield.slash.fill"
        }
    }
}

/// Deterministic categories of home-network & host anomalies.
enum FindingKind: String, Codable, Equatable, Sendable {
    case newDevice
    case gatewayMACChanged
    case deviceIPChanged
    case suspiciousOpenPort
    case newUPnPForward
    case hostProcessHighFanOut
    case hostProcessWildcardListener
    case dnsConfigChanged
    case proxyConfigChanged
    case suspiciousHostsEntry
    case connectivityDegraded
    case externalChattyClient
    case externalProxyDomain
}

/// Short, plain-English explanation produced by AFM (or deterministic fallback).
struct FindingExplanation: Codable, Equatable, Sendable {
    var headline: String
    var whyItMatters: String
    var nextStep: String
    var generatedByAFM: Bool
}

/// A deduplicated alert surfaced in the menu bar and Inspector.
struct Finding: Codable, Equatable, Sendable, Identifiable {
    var id: UUID
    /// Stable dedupe key, e.g. "suspiciousOpenPort:aa:bb:cc:dd:ee:ff:5555".
    var dedupeKey: String
    var networkID: String
    var kind: FindingKind
    var severity: FindingSeverity
    var title: String
    var summary: String
    var evidence: [String]
    /// Optional subject identifier (MAC address, process name, or mapping ID) for Trust/Mute.
    var subjectID: String?
    var firstSeen: Date
    var lastSeen: Date
    var isAcknowledged: Bool
    var explanation: FindingExplanation?

    init(
        id: UUID = UUID(),
        dedupeKey: String,
        networkID: String,
        kind: FindingKind,
        severity: FindingSeverity,
        title: String,
        summary: String,
        evidence: [String],
        subjectID: String? = nil,
        firstSeen: Date = Date(),
        lastSeen: Date = Date(),
        isAcknowledged: Bool = false,
        explanation: FindingExplanation? = nil
    ) {
        self.id = id
        self.dedupeKey = dedupeKey
        self.networkID = networkID
        self.kind = kind
        self.severity = severity
        self.title = title
        self.summary = summary
        self.evidence = evidence
        self.subjectID = subjectID
        self.firstSeen = firstSeen
        self.lastSeen = lastSeen
        self.isAcknowledged = isAcknowledged
        self.explanation = explanation
    }

    var displayHeadline: String {
        explanation?.headline ?? title
    }

    var displayBody: String {
        explanation?.whyItMatters ?? summary
    }
}

/// Allows users to permanently silence a specific finding key or subject.
struct MuteRule: Codable, Equatable, Hashable, Sendable, Identifiable {
    var id: UUID
    var networkID: String
    var dedupeKey: String
    var label: String
    var createdAt: Date

    init(
        id: UUID = UUID(),
        networkID: String,
        dedupeKey: String,
        label: String,
        createdAt: Date = Date()
    ) {
        self.id = id
        self.networkID = networkID
        self.dedupeKey = dedupeKey
        self.label = label
        self.createdAt = createdAt
    }
}

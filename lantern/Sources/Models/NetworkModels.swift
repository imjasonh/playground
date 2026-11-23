import Foundation

/// Identifies a local network so baselines stay isolated (home vs. coffee shop).
struct NetworkIdentity: Codable, Equatable, Hashable, Sendable {
    /// Stable key: gateway MAC when known, otherwise gateway IP + interface.
    var id: String
    var ssid: String?
    var gatewayIP: String?
    var gatewayMAC: String?
    var localIP: String?
    var interfaceName: String?
    var subnetPrefix: String? // e.g. "192.168.1"

    var displayName: String {
        if let ssid, !ssid.isEmpty { return ssid }
        if let gw = gatewayIP, !gw.isEmpty { return "LAN (\(gw))" }
        if let iface = interfaceName, !iface.isEmpty { return iface }
        return "Offline"
    }

    static let offline = NetworkIdentity(
        id: "offline",
        ssid: nil,
        gatewayIP: nil,
        gatewayMAC: nil,
        localIP: nil,
        interfaceName: nil,
        subnetPrefix: nil
    )
}

enum NetworkTrust: String, Codable, Equatable, Sendable, CaseIterable {
    /// User's home / trusted LAN: full anomaly alerting & notifications.
    case trusted
    /// Public / hotel / cafe Wi-Fi: quiet mode (connectivity checks only, no new-device spam).
    case untrusted
    /// Not yet classified by the user; defaults to quiet notifications until marked trusted.
    case unknown

    var label: String {
        switch self {
        case .trusted: return "Trusted LAN"
        case .untrusted: return "Untrusted / Public"
        case .unknown: return "Unclassified"
        }
    }
}

/// High-signal suspicious or notable TCP port discovered on a LAN host.
struct OpenPort: Codable, Equatable, Hashable, Sendable, Identifiable {
    var port: UInt16
    var serviceName: String
    var isSuspicious: Bool

    var id: UInt16 { port }
}

/// Cached on-device (or deterministic) classification for a LAN device.
struct DeviceClassification: Codable, Equatable, Sendable {
    var friendlyName: String
    var category: String
    var riskNote: String?
    var source: Source

    enum Source: String, Codable, Equatable, Sendable {
        case foundationModel
        case heuristic
    }
}

/// A host observed on the local network via ARP, mDNS, or SSDP.
struct LANDevice: Codable, Equatable, Sendable, Identifiable {
    /// Normalized lowercase MAC address (`aa:bb:cc:dd:ee:ff`), or IP fallback when MAC unavailable.
    var id: String
    var macAddress: String
    var ipAddress: String
    var hostname: String?
    var vendor: String?
    var mdnsServices: [String]
    var openPorts: [OpenPort]
    var isGateway: Bool
    var isThisMac: Bool
    var firstSeen: Date
    var lastSeen: Date
    var isTrusted: Bool
    var customLabel: String?
    var classification: DeviceClassification?

    var displayName: String {
        if let customLabel, !customLabel.isEmpty { return customLabel }
        if let friendly = classification?.friendlyName, !friendly.isEmpty { return friendly }
        if let hostname, !hostname.isEmpty { return hostname }
        if let vendor, !vendor.isEmpty { return "\(vendor) (\(ipAddress))" }
        return ipAddress
    }

    var suspiciousPorts: [OpenPort] {
        openPorts.filter(\.isSuspicious)
    }
}

/// Active inbound port forward reported by the router via UPnP IGD.
struct UPnPMapping: Codable, Equatable, Hashable, Sendable, Identifiable {
    var externalPort: UInt16
    var internalPort: UInt16
    var internalClient: String
    var protocolName: String // "TCP" or "UDP"
    var description: String
    var enabled: Bool
    var leaseDuration: Int

    var id: String {
        "\(protocolName):\(externalPort)->\(internalClient):\(internalPort)"
    }
}

/// Per-process network behavior observed on *this* Mac (`lsof` + `nettop`).
struct ProcessNetworkSnapshot: Codable, Equatable, Sendable, Identifiable {
    var pid: Int32
    var processName: String
    var uniqueRemoteIPs: Int
    var uniqueRemoteSubnets: Int // /16 prefixes — strong residential-proxy fan-out signal
    var establishedConnections: Int
    var bytesIn: UInt64
    var bytesOut: UInt64
    var listeningWildcardPorts: [UInt16] // bound to 0.0.0.0 / :: / *
    var sampleRemoteEndpoints: [String]

    var id: String { "\(processName)#\(pid)" }

    /// Ratio of outbound bytes to total bytes when traffic is non-trivial.
    var uploadRatio: Double {
        let total = bytesIn + bytesOut
        guard total > 0 else { return 0 }
        return Double(bytesOut) / Double(total)
    }
}

/// Distilled connectivity health snapshot (the best of Onramp, now automatic).
struct ConnectivityHealth: Codable, Equatable, Sendable {
    var isPathSatisfied: Bool
    var defaultInterface: String?
    var defaultGateway: String?
    var isVPNActive: Bool
    var vpnInterfaces: [String]
    var dnsServers: [String]
    var proxyEnabled: Bool
    var proxySummary: String?
    var suspiciousHostsEntries: [String]
    var dnsResolves: Bool?
    var httpProbeOK: Bool?
    var captivePortalSuspected: Bool
    var checkedAt: Date

    var looksHealthy: Bool {
        isPathSatisfied && (dnsResolves ?? true) && (httpProbeOK ?? true) && !captivePortalSuspected
    }

    var statusLabel: String {
        if !isPathSatisfied { return "Offline" }
        if captivePortalSuspected { return "Captive portal" }
        if dnsResolves == false { return "DNS failing" }
        if httpProbeOK == false { return "No internet" }
        return "Online"
    }

    static let unknown = ConnectivityHealth(
        isPathSatisfied: true,
        defaultInterface: nil,
        defaultGateway: nil,
        isVPNActive: false,
        vpnInterfaces: [],
        dnsServers: [],
        proxyEnabled: false,
        proxySummary: nil,
        suspiciousHostsEntries: [],
        dnsResolves: nil,
        httpProbeOK: nil,
        captivePortalSuspected: false,
        checkedAt: .distantPast
    )
}

/// Optional external vantage point (Pi-hole / AdGuard Home / Router API) summary.
struct ExternalVantageSnapshot: Codable, Equatable, Sendable {
    struct ChattyClient: Codable, Equatable, Sendable, Identifiable {
        var clientIP: String
        var clientName: String?
        var queryCount: Int
        var blockedCount: Int
        var suspiciousDomains: [String]

        var id: String { clientIP }
    }

    var sourceName: String
    var fetchedAt: Date
    var chattyClients: [ChattyClient]
    var errorMessage: String?
}

/// Complete point-in-time observation passed into the deterministic AnomalyDetector.
struct WatchSnapshot: Equatable, Sendable {
    var capturedAt: Date
    var network: NetworkIdentity
    var devices: [LANDevice]
    var upnpMappings: [UPnPMapping]
    var hostProcesses: [ProcessNetworkSnapshot]
    var connectivity: ConnectivityHealth
    var externalVantage: ExternalVantageSnapshot?
}

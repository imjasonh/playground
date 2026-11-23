import Foundation

/// Pure deterministic anomaly engine.
/// Evaluates a `WatchSnapshot` against the persisted `NetworkBaseline` and returns
/// structured `Finding`s plus the updated baseline.
enum AnomalyDetector {
    struct Thresholds: Equatable, Sendable {
        /// Unique `/16` remote subnets to flag residential-proxy-style fan-out on this Mac.
        var highFanOutSubnets: Int = 12
        var highFanOutIPs: Int = 15
        /// Lower fan-out threshold when combined with heavy upload ratio.
        var uploadFanOutSubnets: Int = 6
        var uploadRatioThreshold: Double = 0.65
        var uploadBytesThreshold: UInt64 = 5 * 1024 * 1024 // 5 MB
        /// External DNS query threshold (Pi-hole / AdGuard Home).
        var chattyDNSQueries: Int = 5_000
    }

    struct EvaluationResult: Equatable, Sendable {
        var updatedBaseline: NetworkBaseline
        var emittedFindings: [Finding]
    }

    /// Expected macOS system processes & browsers that legitimately talk to many IPs or listen on LAN.
    static let defaultIgnoredFanOutProcesses: Set<String> = [
        "safari", "google chrome", "google chrome helper", "firefox", "arc", "brave browser",
        "com.apple.webkit.networking", "nsurlsessiond", "cloudd", "trustd", "mdnsresponder",
        "apsd", "rapportd", "identityservicesd",
    ]

    static let defaultIgnoredWildcardListeners: Set<String> = [
        "mdnsresponder", "rapportd", "airplayxpchelper", "controlcenter", "sharingd",
        "identityservicesd", "wifivelocityd", "netbiosd", "launchd",
    ]

    static let highRiskUPnPPorts: Set<UInt16> = [22, 23, 445, 1080, 3128, 3389, 5555, 5900, 8080, 9050]

    static func evaluate(
        snapshot: WatchSnapshot,
        baseline: NetworkBaseline,
        muteRules: [MuteRule],
        thresholds: Thresholds = Thresholds()
    ) -> EvaluationResult {
        var next = baseline
        let now = snapshot.capturedAt
        let netID = snapshot.network.id
        let isFirstBaselinePass = next.knownDevices.isEmpty && next.gatewayMAC == nil
        let quietPublicMode = (next.trust == .untrusted)

        var findings: [Finding] = []
        let mutedKeys = Set(muteRules.filter { $0.networkID == netID }.map(\.dedupeKey))

        func emit(_ finding: Finding) {
            guard !mutedKeys.contains(finding.dedupeKey) else { return }
            findings.append(finding)
        }

        // 1. Gateway MAC change (possible ARP spoofing / rogue router)
        if let currentGWMAC = snapshot.network.gatewayMAC {
            if let priorGWMAC = next.gatewayMAC, priorGWMAC != currentGWMAC {
                emit(
                    Finding(
                        dedupeKey: "gatewayMACChanged:\(netID)",
                        networkID: netID,
                        kind: .gatewayMACChanged,
                        severity: .critical,
                        title: "Router MAC address changed",
                        summary: "Default gateway \(snapshot.network.gatewayIP ?? "") changed MAC from \(priorGWMAC) to \(currentGWMAC).",
                        evidence: [
                            "Previous gateway MAC: \(priorGWMAC)",
                            "Current gateway MAC: \(currentGWMAC)",
                            "Gateway IP: \(snapshot.network.gatewayIP ?? "unknown")",
                        ],
                        subjectID: currentGWMAC,
                        firstSeen: now,
                        lastSeen: now
                    )
                )
            }
            next.gatewayMAC = currentGWMAC
        }
        if let gwIP = snapshot.network.gatewayIP {
            next.gatewayIP = gwIP
        }

        // 2. LAN devices: new devices + suspicious open ports
        for device in snapshot.devices {
            let prior = next.knownDevices[device.id]
            if prior == nil {
                if !isFirstBaselinePass && !quietPublicMode && !device.isGateway && !device.isThisMac {
                    emit(
                        Finding(
                            dedupeKey: "newDevice:\(device.id)",
                            networkID: netID,
                            kind: .newDevice,
                            severity: .notice,
                            title: "New device joined: \(device.displayName)",
                            summary: "Observed \(device.ipAddress) (\(device.macAddress)) on \(snapshot.network.displayName) for the first time.",
                            evidence: [
                                "IP: \(device.ipAddress)",
                                "MAC: \(device.macAddress)",
                                "Vendor: \(device.vendor ?? "Unknown")",
                            ] + (device.mdnsServices.isEmpty ? [] : ["mDNS: \(device.mdnsServices.joined(separator: ", "))"]),
                            subjectID: device.id,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
            }

            // Suspicious open ports on any untrusted LAN device (even on first pass)
            if !quietPublicMode && !device.isThisMac && !(prior?.isTrusted ?? device.isTrusted) {
                for openPort in device.suspiciousPorts {
                    emit(
                        Finding(
                            dedupeKey: "suspiciousOpenPort:\(device.id):\(openPort.port)",
                            networkID: netID,
                            kind: .suspiciousOpenPort,
                            severity: .warning,
                            title: "\(device.displayName) exposes \(openPort.serviceName) (:\(openPort.port))",
                            summary: "\(device.ipAddress) has port \(openPort.port) (\(openPort.serviceName)) open on the local network.",
                            evidence: [
                                "Device: \(device.displayName) (\(device.ipAddress))",
                                "MAC: \(device.macAddress) (\(device.vendor ?? "Unknown"))",
                                "Open port: \(openPort.port)/tcp (\(openPort.serviceName))",
                            ],
                            subjectID: device.id,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
            }

            // Merge into baseline, preserving trust, custom labels, and cached AFM classifications.
            var merged = device
            if let prior {
                merged.firstSeen = prior.firstSeen
                merged.isTrusted = prior.isTrusted
                merged.customLabel = prior.customLabel
                if merged.classification == nil {
                    merged.classification = prior.classification
                }
                if merged.openPorts.isEmpty && !prior.openPorts.isEmpty {
                    merged.openPorts = prior.openPorts
                }
                if merged.hostname == nil {
                    merged.hostname = prior.hostname
                }
            }
            next.knownDevices[device.id] = merged
        }

        // 3. UPnP inbound port forwards
        if !quietPublicMode {
            for mapping in snapshot.upnpMappings where mapping.enabled {
                let isNew = next.knownUPnPMappings[mapping.id] == nil
                let isHighRisk = highRiskUPnPPorts.contains(mapping.externalPort)
                    || highRiskUPnPPorts.contains(mapping.internalPort)

                if isHighRisk || (!isFirstBaselinePass && isNew) {
                    emit(
                        Finding(
                            dedupeKey: "upnp:\(mapping.id)",
                            networkID: netID,
                            kind: .newUPnPForward,
                            severity: isHighRisk ? .critical : .warning,
                            title: "UPnP port forward to \(mapping.internalClient):\(mapping.internalPort)",
                            summary: "Router is forwarding external \(mapping.protocolName) port \(mapping.externalPort) to \(mapping.internalClient):\(mapping.internalPort).",
                            evidence: [
                                "Mapping: \(mapping.protocolName) :\(mapping.externalPort) → \(mapping.internalClient):\(mapping.internalPort)",
                                "Description: \(mapping.description.isEmpty ? "(none)" : mapping.description)",
                                "Lease: \(mapping.leaseDuration == 0 ? "permanent" : "\(mapping.leaseDuration)s")",
                            ],
                            subjectID: mapping.internalClient,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
                next.knownUPnPMappings[mapping.id] = mapping
            }
        }

        // 4. This Mac's own processes (residential-proxy fan-out & wildcard listeners)
        for proc in snapshot.hostProcesses {
            let lowerName = proc.processName.lowercased()
            let isTrustedProc = next.trustedProcesses.contains(proc.processName)

            if !isTrustedProc && !defaultIgnoredFanOutProcesses.contains(lowerName) {
                let highFanOut = proc.uniqueRemoteSubnets >= thresholds.highFanOutSubnets
                    && proc.uniqueRemoteIPs >= thresholds.highFanOutIPs
                let uploadHeavyProxy = proc.uniqueRemoteSubnets >= thresholds.uploadFanOutSubnets
                    && proc.uploadRatio >= thresholds.uploadRatioThreshold
                    && proc.bytesOut >= thresholds.uploadBytesThreshold

                if highFanOut || uploadHeavyProxy {
                    let outMB = String(format: "%.1f MB", Double(proc.bytesOut) / 1_048_576.0)
                    let ratioPct = Int((proc.uploadRatio * 100).rounded())
                    emit(
                        Finding(
                            dedupeKey: "hostFanOut:\(proc.processName)",
                            networkID: netID,
                            kind: .hostProcessHighFanOut,
                            severity: uploadHeavyProxy ? .critical : .warning,
                            title: "\(proc.processName) talking to \(proc.uniqueRemoteIPs) external IPs",
                            summary: "This Mac's process '\(proc.processName)' has high external IP diversity (\(proc.uniqueRemoteSubnets) /16 subnets), a pattern associated with P2P or residential-proxy SDKs.",
                            evidence: [
                                "Process: \(proc.processName) (PID \(proc.pid))",
                                "Remote fan-out: \(proc.uniqueRemoteIPs) IPs across \(proc.uniqueRemoteSubnets) /16 subnets",
                                "Traffic: \(outMB) out (\(ratioPct)% upload ratio)",
                            ] + (proc.sampleRemoteEndpoints.isEmpty ? [] : ["Sample peers: \(proc.sampleRemoteEndpoints.prefix(3).joined(separator: ", "))"]),
                            subjectID: proc.processName,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
            }

            if !isTrustedProc && !defaultIgnoredWildcardListeners.contains(lowerName) {
                for port in proc.listeningWildcardPorts {
                    let listenerKey = "\(proc.processName):\(port)"
                    if !next.trustedListeners.contains(listenerKey) && !isFirstBaselinePass {
                        emit(
                            Finding(
                                dedupeKey: "hostListener:\(listenerKey)",
                                networkID: netID,
                                kind: .hostProcessWildcardListener,
                                severity: .notice,
                                title: "\(proc.processName) listening on LAN port :\(port)",
                                summary: "Process '\(proc.processName)' opened a wildcard listener (0.0.0.0 / ::) on port \(port), reachable by other devices on this network.",
                                evidence: [
                                    "Process: \(proc.processName) (PID \(proc.pid))",
                                    "Listening port: *:\(port)",
                                ],
                                subjectID: proc.processName,
                                firstSeen: now,
                                lastSeen: now
                            )
                        )
                    }
                }
            }
        }

        // 5. Connectivity, DNS, proxy, and /etc/hosts drift
        let conn = snapshot.connectivity
        if !next.dnsServers.isEmpty && !conn.dnsServers.isEmpty && next.dnsServers != conn.dnsServers {
            emit(
                Finding(
                    dedupeKey: "dnsChanged:\(netID):\(conn.dnsServers.joined(separator: ","))",
                    networkID: netID,
                    kind: .dnsConfigChanged,
                    severity: .warning,
                    title: "DNS servers changed",
                    summary: "System DNS resolvers changed from \(next.dnsServers.joined(separator: ", ")) to \(conn.dnsServers.joined(separator: ", ")).",
                    evidence: [
                        "Previous DNS: \(next.dnsServers.joined(separator: ", "))",
                        "Current DNS: \(conn.dnsServers.joined(separator: ", "))",
                    ],
                    firstSeen: now,
                    lastSeen: now
                )
            )
        }
        if !conn.dnsServers.isEmpty {
            next.dnsServers = conn.dnsServers
        }

        if !next.proxyEnabled && conn.proxyEnabled {
            emit(
                Finding(
                    dedupeKey: "proxyEnabled:\(netID):\(conn.proxySummary ?? "proxy")",
                    networkID: netID,
                    kind: .proxyConfigChanged,
                    severity: .warning,
                    title: "System network proxy enabled",
                    summary: "macOS proxy settings became active: \(conn.proxySummary ?? "configured").",
                    evidence: ["Active proxy: \(conn.proxySummary ?? "enabled")"],
                    firstSeen: now,
                    lastSeen: now
                )
            )
        }
        next.proxyEnabled = conn.proxyEnabled

        if !conn.suspiciousHostsEntries.isEmpty {
            emit(
                Finding(
                    dedupeKey: "hostsFile:\(conn.suspiciousHostsEntries.count)",
                    networkID: netID,
                    kind: .suspiciousHostsEntry,
                    severity: .info,
                    title: "\(conn.suspiciousHostsEntries.count) custom /etc/hosts override(s)",
                    summary: "/etc/hosts contains non-standard hostname mappings that bypass normal DNS.",
                    evidence: Array(conn.suspiciousHostsEntries.prefix(5)),
                    firstSeen: now,
                    lastSeen: now
                )
            )
        }

        if !conn.looksHealthy {
            var reasons: [String] = []
            if !conn.isPathSatisfied { reasons.append("No active network path") }
            if conn.captivePortalSuspected { reasons.append("Captive portal login required") }
            if conn.dnsResolves == false { reasons.append("DNS resolution failed") }
            if conn.httpProbeOK == false { reasons.append("HTTP probe unreachable") }
            if conn.isVPNActive { reasons.append("VPN active (\(conn.vpnInterfaces.joined(separator: ", ")))") }

            emit(
                Finding(
                    dedupeKey: "connectivity:\(conn.statusLabel)",
                    networkID: netID,
                    kind: .connectivityDegraded,
                    severity: .warning,
                    title: "Connectivity issue: \(conn.statusLabel)",
                    summary: reasons.joined(separator: ". "),
                    evidence: reasons + (conn.dnsServers.isEmpty ? [] : ["DNS: \(conn.dnsServers.joined(separator: ", "))"]),
                    firstSeen: now,
                    lastSeen: now
                )
            )
        }

        // 6. Optional External Vantage (Pi-hole / AdGuard Home)
        if let external = snapshot.externalVantage, external.errorMessage == nil {
            for client in external.chattyClients {
                let label = client.clientName ?? client.clientIP
                if !client.suspiciousDomains.isEmpty {
                    emit(
                        Finding(
                            dedupeKey: "externalProxyDomain:\(client.clientIP):\(client.suspiciousDomains.first ?? "")",
                            networkID: netID,
                            kind: .externalProxyDomain,
                            severity: .critical,
                            title: "Residential proxy domain queried on LAN",
                            summary: "\(external.sourceName) observed DNS lookups for known residential-proxy broker domains.",
                            evidence: [
                                "Source: \(external.sourceName)",
                                "Client: \(label)",
                                "Domains: \(client.suspiciousDomains.prefix(4).joined(separator: ", "))",
                            ],
                            subjectID: client.clientIP,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
                if client.queryCount >= thresholds.chattyDNSQueries {
                    emit(
                        Finding(
                            dedupeKey: "externalChatty:\(client.clientIP)",
                            networkID: netID,
                            kind: .externalChattyClient,
                            severity: .warning,
                            title: "Very chatty device: \(label)",
                            summary: "\(label) sent \(client.queryCount) DNS queries via \(external.sourceName).",
                            evidence: [
                                "Source: \(external.sourceName)",
                                "Client: \(label)",
                                "Queries: \(client.queryCount)",
                            ],
                            subjectID: client.clientIP,
                            firstSeen: now,
                            lastSeen: now
                        )
                    )
                }
            }
        }

        next.lastSeen = now
        return EvaluationResult(updatedBaseline: next, emittedFindings: findings)
    }
}

import Foundation

/// Optional read-only connector for Pi-hole or AdGuard Home DNS logs (Phase 4).
/// Gives Lantern true LAN-wide visibility into chatty IoT devices and residential-proxy broker domains.
enum ExternalVantageCollector {
    /// Curated residential-proxy / bandwidth-sharing broker domain suffixes.
    static let knownProxyBrokerSuffixes: [String] = [
        "honeygain.com",
        "packetstream.io",
        "iproyal.com",
        "pawns.app",
        "earnapp.com",
        "brightdata.com",
        "luminati.io",
        "peer2profit.com",
        "peer2profit.io",
        "traffmonetizer.com",
        "repocket.co",
        "packetshare.io",
        "mystnodes.com",
        "mysterium.network",
        "grass.io",
        "getgrass.io",
        "proxylite.ru",
    ]

    static func collect(config: ExternalVantageConfig, now: Date = Date()) async -> ExternalVantageSnapshot? {
        guard config.provider != .none else { return nil }
        let trimmedBase = config.baseURL.trimmingCharacters(in: .whitespacesAndNewlines)
            .trimmingCharacters(in: CharacterSet(charactersIn: "/"))
        guard !trimmedBase.isEmpty else { return nil }

        switch config.provider {
        case .none:
            return nil
        case .pihole:
            return await fetchPihole(baseURL: trimmedBase, token: config.apiToken, now: now)
        case .adguardHome:
            return await fetchAdGuard(baseURL: trimmedBase, token: config.apiToken, now: now)
        }
    }

    static func matchesProxyBrokerDomain(_ domain: String) -> Bool {
        let lower = domain.lowercased().trimmingCharacters(in: CharacterSet(charactersIn: "."))
        return knownProxyBrokerSuffixes.contains { suffix in
            lower == suffix || lower.hasSuffix("." + suffix)
        }
    }

    // MARK: - Pure parsers (unit-tested)

    /// Parses Pi-hole v5/v6 top-clients JSON (`top_sources` or `clients`).
    static func parsePiholeTopClients(_ data: Data, now: Date = Date()) -> ExternalVantageSnapshot {
        guard let obj = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            return ExternalVantageSnapshot(
                sourceName: "Pi-hole",
                fetchedAt: now,
                chattyClients: [],
                errorMessage: "Unrecognized JSON from Pi-hole"
            )
        }

        var clients: [ExternalVantageSnapshot.ChattyClient] = []
        if let topSources = obj["top_sources"] as? [String: Int] {
            for (key, count) in topSources {
                let parts = key.split(separator: "|", maxSplits: 1).map(String.init)
                let ip = parts.count == 2 ? parts[1] : parts[0]
                let name = parts.count == 2 && !parts[0].isEmpty ? parts[0] : nil
                clients.append(
                    ExternalVantageSnapshot.ChattyClient(
                        clientIP: ip,
                        clientName: name,
                        queryCount: count,
                        blockedCount: 0,
                        suspiciousDomains: []
                    )
                )
            }
        } else if let list = obj["clients"] as? [[String: Any]] {
            for item in list {
                guard let ip = item["ip"] as? String else { continue }
                let count = item["count"] as? Int ?? 0
                let name = item["name"] as? String
                clients.append(
                    ExternalVantageSnapshot.ChattyClient(
                        clientIP: ip,
                        clientName: name,
                        queryCount: count,
                        blockedCount: 0,
                        suspiciousDomains: []
                    )
                )
            }
        }

        return ExternalVantageSnapshot(
            sourceName: "Pi-hole",
            fetchedAt: now,
            chattyClients: clients.sorted { $0.queryCount > $1.queryCount },
            errorMessage: nil
        )
    }

    /// Parses AdGuard Home `/control/stats` JSON (`top_clients`, `top_queried_domains`).
    static func parseAdGuardStats(_ data: Data, now: Date = Date()) -> ExternalVantageSnapshot {
        guard let obj = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            return ExternalVantageSnapshot(
                sourceName: "AdGuard Home",
                fetchedAt: now,
                chattyClients: [],
                errorMessage: "Unrecognized JSON from AdGuard Home"
            )
        }

        var suspiciousDomains: [String] = []
        if let topDomains = obj["top_queried_domains"] as? [[String: Int]] {
            for entry in topDomains {
                for domain in entry.keys where matchesProxyBrokerDomain(domain) {
                    suspiciousDomains.append(domain)
                }
            }
        }

        var clients: [ExternalVantageSnapshot.ChattyClient] = []
        if let topClients = obj["top_clients"] as? [[String: Int]] {
            for entry in topClients {
                for (ip, count) in entry {
                    clients.append(
                        ExternalVantageSnapshot.ChattyClient(
                            clientIP: ip,
                            clientName: nil,
                            queryCount: count,
                            blockedCount: 0,
                            suspiciousDomains: suspiciousDomains
                        )
                    )
                }
            }
        }

        return ExternalVantageSnapshot(
            sourceName: "AdGuard Home",
            fetchedAt: now,
            chattyClients: clients.sorted { $0.queryCount > $1.queryCount },
            errorMessage: nil
        )
    }

    // MARK: - HTTP fetches

    private static func fetchPihole(baseURL: String, token: String, now: Date) async -> ExternalVantageSnapshot {
        var urlString = "\(baseURL)/admin/api.php?getQuerySources"
        if !token.isEmpty {
            urlString += "&auth=\(token)"
        }
        guard let url = URL(string: urlString) else {
            return ExternalVantageSnapshot(sourceName: "Pi-hole", fetchedAt: now, chattyClients: [], errorMessage: "Invalid Pi-hole URL")
        }
        var req = URLRequest(url: url, timeoutInterval: 4)
        req.httpMethod = "GET"
        do {
            let (data, _) = try await URLSession.shared.data(for: req)
            return parsePiholeTopClients(data, now: now)
        } catch {
            return ExternalVantageSnapshot(sourceName: "Pi-hole", fetchedAt: now, chattyClients: [], errorMessage: error.localizedDescription)
        }
    }

    private static func fetchAdGuard(baseURL: String, token: String, now: Date) async -> ExternalVantageSnapshot {
        guard let url = URL(string: "\(baseURL)/control/stats") else {
            return ExternalVantageSnapshot(sourceName: "AdGuard Home", fetchedAt: now, chattyClients: [], errorMessage: "Invalid AdGuard Home URL")
        }
        var req = URLRequest(url: url, timeoutInterval: 4)
        req.httpMethod = "GET"
        if !token.isEmpty {
            // Supports either raw "user:pass" or pre-encoded Basic token.
            let encoded = token.contains(":") ? Data(token.utf8).base64EncodedString() : token
            req.setValue("Basic \(encoded)", forHTTPHeaderField: "Authorization")
        }
        do {
            let (data, _) = try await URLSession.shared.data(for: req)
            return parseAdGuardStats(data, now: now)
        } catch {
            return ExternalVantageSnapshot(sourceName: "AdGuard Home", fetchedAt: now, chattyClients: [], errorMessage: error.localizedDescription)
        }
    }
}

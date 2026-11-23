import Foundation

/// Observes *this* Mac's per-process network connections, remote IP/subnet fan-out,
/// upload/download byte counts, and wildcard listening sockets (`lsof` + `nettop`).
/// Designed to surface residential-proxy SDKs, unexpected servers, and chatty background apps.
enum HostTrafficCollector {
    static func collect() -> [ProcessNetworkSnapshot] {
        let lsofOut = (try? ProcessRunner.run(
            "/usr/sbin/lsof",
            arguments: ["-i", "-n", "-P"],
            timeoutSeconds: 6,
            maxOutputBytes: 512_000
        ))?.stdout ?? ""

        let nettopOut = (try? ProcessRunner.run(
            "/usr/bin/nettop",
            arguments: ["-P", "-L", "1", "-x", "-J", "bytes_in,bytes_out"],
            timeoutSeconds: 6,
            maxOutputBytes: 256_000
        ))?.stdout ?? ""

        let byteTotals = parseNettop(nettopOut)
        return parseLsof(lsofOut, byteTotalsByPID: byteTotals)
    }

    // MARK: - Pure parsers (unit-tested)

    /// Parses `nettop -P -L 1 -x -J bytes_in,bytes_out` CSV lines:
    /// `,bytes_in,bytes_out,`
    /// `Safari.1234,1048576,204800,`
    static func parseNettop(_ stdout: String) -> [Int32: (bytesIn: UInt64, bytesOut: UInt64)] {
        var totals: [Int32: (UInt64, UInt64)] = [:]
        for rawLine in stdout.split(separator: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespacesAndNewlines)
            guard !line.isEmpty, !line.hasPrefix(",") else { continue }
            let cols = line.split(separator: ",", omittingEmptySubsequences: false)
            guard cols.count >= 3 else { continue }
            let procCol = String(cols[0])
            guard let dotIdx = procCol.lastIndex(of: "."),
                  let pid = Int32(procCol[procCol.index(after: dotIdx)...])
            else { continue }

            let bytesIn = UInt64(cols[1].trimmingCharacters(in: .whitespaces)) ?? 0
            let bytesOut = UInt64(cols[2].trimmingCharacters(in: .whitespaces)) ?? 0
            totals[pid] = (bytesIn, bytesOut)
        }
        return totals
    }

    /// Parses `lsof -i -n -P` output into per-process snapshots.
    static func parseLsof(
        _ stdout: String,
        byteTotalsByPID: [Int32: (bytesIn: UInt64, bytesOut: UInt64)] = [:]
    ) -> [ProcessNetworkSnapshot] {
        struct Accumulator {
            var pid: Int32
            var name: String
            var remoteIPs: Set<String> = []
            var remoteSubnets: Set<String> = []
            var established: Int = 0
            var wildcardListeners: Set<UInt16> = []
            var sampleEndpoints: [String] = []
        }

        var byPID: [Int32: Accumulator] = [:]

        for rawLine in stdout.split(separator: "\n").dropFirst() {
            let tokens = rawLine.split(whereSeparator: { $0 == " " || $0 == "\t" })
            guard tokens.count >= 9 else { continue }
            let rawName = String(tokens[0]).replacingOccurrences(of: "\\x20", with: " ")
            guard let pid = Int32(tokens[1]) else { continue }

            // Reconstruct NAME column (tokens from index 8 onward, e.g. `192.168.1.5:52010->1.1.1.1:443 (ESTABLISHED)`).
            let namePart = tokens[8...].joined(separator: " ")

            var acc = byPID[pid] ?? Accumulator(pid: pid, name: rawName)

            if namePart.contains("(LISTEN)") {
                let endpoint = namePart.replacingOccurrences(of: "(LISTEN)", with: "")
                    .trimmingCharacters(in: .whitespaces)
                if let port = extractWildcardListenPort(endpoint) {
                    acc.wildcardListeners.insert(port)
                }
            } else if let arrowRange = namePart.range(of: "->") {
                let rightSide = namePart[arrowRange.upperBound...]
                let remoteEndpoint = rightSide.split(separator: " ").first.map(String.init) ?? ""
                if let remoteIP = extractHost(from: remoteEndpoint),
                   !isLoopbackOrLocal(remoteIP)
                {
                    acc.remoteIPs.insert(remoteIP)
                    if let subnet = subnetKey(for: remoteIP) {
                        acc.remoteSubnets.insert(subnet)
                    }
                    if namePart.contains("(ESTABLISHED)") {
                        acc.established += 1
                    }
                    if acc.sampleEndpoints.count < 8, !acc.sampleEndpoints.contains(remoteEndpoint) {
                        acc.sampleEndpoints.append(remoteEndpoint)
                    }
                }
            }

            byPID[pid] = acc
        }

        return byPID.values.compactMap { acc -> ProcessNetworkSnapshot? in
            let totals = byteTotalsByPID[acc.pid] ?? (0, 0)
            guard !acc.remoteIPs.isEmpty || !acc.wildcardListeners.isEmpty || totals.bytesIn + totals.bytesOut > 0 else {
                return nil
            }
            return ProcessNetworkSnapshot(
                pid: acc.pid,
                processName: acc.name,
                uniqueRemoteIPs: acc.remoteIPs.count,
                uniqueRemoteSubnets: acc.remoteSubnets.count,
                establishedConnections: acc.established,
                bytesIn: totals.bytesIn,
                bytesOut: totals.bytesOut,
                listeningWildcardPorts: acc.wildcardListeners.sorted(),
                sampleRemoteEndpoints: acc.sampleEndpoints
            )
        }.sorted { lhs, rhs in
            if lhs.uniqueRemoteSubnets != rhs.uniqueRemoteSubnets {
                return lhs.uniqueRemoteSubnets > rhs.uniqueRemoteSubnets
            }
            if lhs.bytesOut != rhs.bytesOut {
                return lhs.bytesOut > rhs.bytesOut
            }
            return lhs.processName.localizedCaseInsensitiveCompare(rhs.processName) == .orderedAscending
        }
    }

    /// Extracts port when a socket listens on wildcard (`*:8080`, `0.0.0.0:1080`, `[::]:5555`).
    static func extractWildcardListenPort(_ endpoint: String) -> UInt16? {
        guard let colonIdx = endpoint.lastIndex(of: ":") else { return nil }
        let host = String(endpoint[..<colonIdx])
        let portStr = String(endpoint[endpoint.index(after: colonIdx)...])
        guard let port = UInt16(portStr) else { return nil }
        if host == "*" || host == "0.0.0.0" || host == "[::]" || host == "::" {
            return port
        }
        return nil
    }

    static func extractHost(from endpoint: String) -> String? {
        if endpoint.hasPrefix("[") {
            guard let close = endpoint.firstIndex(of: "]") else { return nil }
            return String(endpoint[endpoint.index(after: endpoint.startIndex)..<close])
        }
        guard let colon = endpoint.lastIndex(of: ":") else { return nil }
        return String(endpoint[..<colon])
    }

    static func isLoopbackOrLocal(_ ip: String) -> Bool {
        if ip == "::1" || ip.hasPrefix("127.") || ip.hasPrefix("fe80:") { return true }
        if ip.hasPrefix("10.") || ip.hasPrefix("192.168.") { return true }
        if ip.hasPrefix("172.") {
            let parts = ip.split(separator: ".")
            if parts.count >= 2, let second = Int(parts[1]), (16...31).contains(second) {
                return true
            }
        }
        return false
    }

    /// Groups IPv4 by `/16` and IPv6 by first two hextets for fan-out diversity scoring.
    static func subnetKey(for ip: String) -> String? {
        if ip.contains(".") {
            let parts = ip.split(separator: ".")
            guard parts.count == 4 else { return nil }
            return "\(parts[0]).\(parts[1])"
        }
        if ip.contains(":") {
            let parts = ip.split(separator: ":")
            guard parts.count >= 2 else { return nil }
            return "\(parts[0]):\(parts[1])"
        }
        return nil
    }
}

import Darwin
import Foundation
import Network
import Security

/// On-demand active probes for a single user-selected LAN device.
/// NEVER called during background scans — only runs when the user explicitly clicks a probe button.
enum DeviceExplorer {
    struct PingResult: Equatable, Sendable {
        var transmitted: Int
        var received: Int
        var packetLossPercent: Double
        var avgLatencyMs: Double?
        var rawSummary: String
    }

    struct HTTPFingerprint: Equatable, Sendable {
        var url: String
        var statusCode: Int?
        var serverHeader: String?
        var poweredByHeader: String?
        var pageTitle: String?
        var tlsCertSubject: String?
        var errorMessage: String?
    }

    struct BannerResult: Equatable, Sendable {
        var port: UInt16
        var reachable: Bool
        var banner: String?
        var looksLikeOpenProxy: Bool
        var note: String
    }

    /// Expanded port list for user-initiated inspection of one selected host.
    static let interactivePortSpecs: [PortProbeCollector.PortSpec] = PortProbeCollector.defaultSpecs + [
        PortProbeCollector.PortSpec(port: 53, serviceName: "DNS", isSuspicious: false),
        PortProbeCollector.PortSpec(port: 554, serviceName: "RTSP Camera", isSuspicious: false),
        PortProbeCollector.PortSpec(port: 1883, serviceName: "MQTT IoT", isSuspicious: false),
        PortProbeCollector.PortSpec(port: 5000, serviceName: "UPnP / Alt-HTTP", isSuspicious: false),
        PortProbeCollector.PortSpec(port: 8443, serviceName: "Alt-HTTPS", isSuspicious: false),
        PortProbeCollector.PortSpec(port: 9100, serviceName: "Printer JetDirect", isSuspicious: false),
    ]

    // MARK: - 1. ICMP Ping

    static func ping(ip: String) async -> PingResult {
        await Task.detached(priority: .userInitiated) {
            let res = try? ProcessRunner.run(
                "/sbin/ping",
                arguments: ["-c", "4", "-t", "4", ip],
                timeoutSeconds: 6
            )
            return parsePingOutput(res?.stdout ?? res?.stderr ?? "")
        }.value
    }

    static func parsePingOutput(_ output: String) -> PingResult {
        var transmitted = 0
        var received = 0
        var loss = 100.0
        var avgMs: Double?

        for rawLine in output.split(separator: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            if line.contains("packets transmitted") {
                // Example: "4 packets transmitted, 4 packets received, 0.0% packet loss"
                let parts = line.split(separator: ",")
                if parts.count >= 3 {
                    transmitted = Int(parts[0].split(separator: " ").first ?? "") ?? 0
                    received = Int(parts[1].trimmingCharacters(in: .whitespaces).split(separator: " ").first ?? "") ?? 0
                    let lossToken = parts[2].trimmingCharacters(in: .whitespaces).split(separator: "%").first ?? ""
                    loss = Double(lossToken) ?? 100.0
                }
            } else if line.contains("round-trip") || line.contains("rtt ") {
                // Example: "round-trip min/avg/max/stddev = 1.234/2.345/3.456/0.500 ms"
                if let eq = line.firstIndex(of: "=") {
                    let statsPart = line[line.index(after: eq)...].trimmingCharacters(in: .whitespaces)
                    let numbers = statsPart.split(separator: " ").first?.split(separator: "/") ?? []
                    if numbers.count >= 2 {
                        avgMs = Double(numbers[1])
                    }
                }
            }
        }

        let summary: String
        if received > 0, let avgMs {
            summary = String(format: "%d/%d replies (%.0f%% loss), avg %.1f ms", received, transmitted, loss, avgMs)
        } else if received > 0 {
            summary = "\(received)/\(transmitted) replies"
        } else {
            summary = "No ICMP reply (host offline or ICMP blocked)"
        }

        return PingResult(
            transmitted: transmitted,
            received: received,
            packetLossPercent: loss,
            avgLatencyMs: avgMs,
            rawSummary: summary
        )
    }

    // MARK: - 2. HTTP / HTTPS Fingerprint

    static func inspectHTTP(ip: String, port: UInt16 = 80, useHTTPS: Bool = false) async -> HTTPFingerprint {
        let scheme = useHTTPS ? "https" : "http"
        let urlString = "\(scheme)://\(ip):\(port)/"
        guard let url = URL(string: urlString) else {
            return HTTPFingerprint(url: urlString, errorMessage: "Invalid URL")
        }

        let delegate = LANInspectionSessionDelegate()
        let config = URLSessionConfiguration.ephemeral
        config.timeoutIntervalForRequest = 3
        config.timeoutIntervalForResource = 4
        let session = URLSession(configuration: config, delegate: delegate, delegateQueue: nil)
        defer { session.invalidateAndCancel() }

        var req = URLRequest(url: url, timeoutInterval: 3)
        req.httpMethod = "GET"
        req.setValue("Lantern-LAN-Inspector/1.0", forHTTPHeaderField: "User-Agent")

        do {
            let (data, response) = try await session.data(for: req)
            let http = response as? HTTPURLResponse
            let body = String(data: data.prefix(16_384), encoding: .utf8) ?? ""
            return HTTPFingerprint(
                url: urlString,
                statusCode: http?.statusCode,
                serverHeader: http?.value(forHTTPHeaderField: "Server"),
                poweredByHeader: http?.value(forHTTPHeaderField: "X-Powered-By"),
                pageTitle: extractHTMLTitle(from: body),
                tlsCertSubject: delegate.capturedSubject,
                errorMessage: nil
            )
        } catch {
            return HTTPFingerprint(
                url: urlString,
                tlsCertSubject: delegate.capturedSubject,
                errorMessage: error.localizedDescription
            )
        }
    }

    static func extractHTMLTitle(from html: String) -> String? {
        let lower = html.lowercased()
        guard let start = lower.range(of: "<title") else { return nil }
        guard let tagEnd = lower.range(of: ">", range: start.upperBound..<lower.endIndex) else { return nil }
        guard let close = lower.range(of: "</title>", range: tagEnd.upperBound..<lower.endIndex) else { return nil }
        let raw = String(html[tagEnd.upperBound..<close.lowerBound])
        let collapsed = raw
            .replacingOccurrences(of: "\n", with: " ")
            .replacingOccurrences(of: "\r", with: " ")
            .trimmingCharacters(in: .whitespacesAndNewlines)
        return collapsed.isEmpty ? nil : String(collapsed.prefix(120))
    }

    // MARK: - 3. TCP Banner Grab & Open-Proxy Handshake Test

    /// Connects to a TCP port on the device. For SOCKS ports (`1080`/`9050`), sends a benign
    /// 3-byte SOCKS5 greeting (`0x05 0x01 0x00`) to see if an unauthenticated proxy replies (`0x05 0x00`).
    /// For other ports, waits briefly for a service banner (e.g. SSH / Telnet / SMTP).
    static func grabBanner(ip: String, port: UInt16, timeoutSeconds: TimeInterval = 1.5) async -> BannerResult {
        guard let nwPort = NWEndpoint.Port(rawValue: port) else {
            return BannerResult(port: port, reachable: false, banner: nil, looksLikeOpenProxy: false, note: "Invalid port")
        }
        let isSocksPort = (port == 1080 || port == 9050)
        let connection = NWConnection(host: NWEndpoint.Host(ip), port: nwPort, using: .tcp)
        let queue = DispatchQueue(label: "io.github.imjasonh.lantern.banner.\(port)", qos: .userInitiated)

        return await withCheckedContinuation { continuation in
            let lock = NSLock()
            var finished = false

            func finish(_ result: BannerResult) {
                lock.lock()
                defer { lock.unlock() }
                guard !finished else { return }
                finished = true
                connection.stateUpdateHandler = nil
                connection.cancel()
                continuation.resume(returning: result)
            }

            connection.stateUpdateHandler = { state in
                switch state {
                case .ready:
                    if isSocksPort {
                        // Benign SOCKS5 no-auth greeting (does not forward traffic)
                        let greeting = Data([0x05, 0x01, 0x00])
                        connection.send(content: greeting, completion: .contentProcessed { _ in
                            connection.receive(minimumIncompleteLength: 2, maximumLength: 256) { data, _, _, _ in
                                let bytes = [UInt8](data ?? Data())
                                if bytes.count >= 2 && bytes[0] == 0x05 && bytes[1] == 0x00 {
                                    finish(
                                        BannerResult(
                                            port: port,
                                            reachable: true,
                                            banner: "SOCKS5 reply 0x05 0x00 (no-auth accepted)",
                                            looksLikeOpenProxy: true,
                                            note: "Responded as an open unauthenticated SOCKS5 proxy!"
                                        )
                                    )
                                } else if bytes.count >= 2 && bytes[0] == 0x05 {
                                    finish(
                                        BannerResult(
                                            port: port,
                                            reachable: true,
                                            banner: String(format: "SOCKS5 reply 0x%02x 0x%02x", bytes[0], bytes[1]),
                                            looksLikeOpenProxy: false,
                                            note: "SOCKS5 server detected (authentication required or rejected)."
                                        )
                                    )
                                } else {
                                    let text = sanitizeBanner(data ?? Data())
                                    finish(
                                        BannerResult(
                                            port: port,
                                            reachable: true,
                                            banner: text,
                                            looksLikeOpenProxy: false,
                                            note: "Port open; did not reply with SOCKS5 handshake."
                                        )
                                    )
                                }
                            }
                        })
                    } else {
                        connection.receive(minimumIncompleteLength: 1, maximumLength: 512) { data, _, _, _ in
                            let text = sanitizeBanner(data ?? Data())
                            finish(
                                BannerResult(
                                    port: port,
                                    reachable: true,
                                    banner: text,
                                    looksLikeOpenProxy: false,
                                    note: text == nil ? "Port open (no initial banner sent)." : "Received service banner."
                                )
                            )
                        }
                    }
                case .failed:
                    finish(
                        BannerResult(
                            port: port,
                            reachable: false,
                            banner: nil,
                            looksLikeOpenProxy: false,
                            note: "Connection refused or unreachable."
                        )
                    )
                default:
                    break
                }
            }
            connection.start(queue: queue)

            queue.asyncAfter(deadline: .now() + timeoutSeconds) {
                finish(
                    BannerResult(
                        port: port,
                        reachable: true,
                        banner: nil,
                        looksLikeOpenProxy: false,
                        note: "Timed out waiting for banner."
                    )
                )
            }
        }
    }

    static func sanitizeBanner(_ data: Data) -> String? {
        guard !data.isEmpty else { return nil }
        let scalars = data.compactMap { byte -> Character? in
            if byte == 0x0A || byte == 0x0D || (byte >= 0x20 && byte <= 0x7E) {
                return Character(UnicodeScalar(byte))
            }
            return nil
        }
        let cleaned = String(scalars).trimmingCharacters(in: .whitespacesAndNewlines)
        return cleaned.isEmpty ? nil : String(cleaned.prefix(240))
    }

    // MARK: - 4. Wake-on-LAN

    static func buildWakeOnLANPacket(mac: String) -> Data? {
        guard let norm = OUILookup.normalizeMAC(mac) else { return nil }
        let macBytes = norm.split(separator: ":").compactMap { UInt8($0, radix: 16) }
        guard macBytes.count == 6 else { return nil }
        var packet = Data(repeating: 0xFF, count: 6)
        for _ in 0..<16 {
            packet.append(contentsOf: macBytes)
        }
        return packet
    }

    static func sendWakeOnLAN(mac: String) -> Bool {
        guard let packet = buildWakeOnLANPacket(mac: mac) else { return false }
        let fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)
        guard fd >= 0 else { return false }
        defer { close(fd) }

        var broadcast: Int32 = 1
        setsockopt(fd, SOL_SOCKET, SO_BROADCAST, &broadcast, socklen_t(MemoryLayout<Int32>.size))

        var addr = sockaddr_in()
        addr.sin_len = UInt8(MemoryLayout<sockaddr_in>.size)
        addr.sin_family = sa_family_t(AF_INET)
        addr.sin_port = UInt16(9).bigEndian
        guard inet_pton(AF_INET, "255.255.255.255", &addr.sin_addr) == 1 else { return false }

        let sent = packet.withUnsafeBytes { buf in
            withUnsafePointer(to: &addr) { ptr in
                ptr.withMemoryRebound(to: sockaddr.self, capacity: 1) { sockPtr in
                    sendto(fd, buf.baseAddress, buf.count, 0, sockPtr, socklen_t(MemoryLayout<sockaddr_in>.size))
                }
            }
        }
        return sent == packet.count
    }
}

/// Ephemeral delegate that inspects self-signed LAN HTTPS certs without bypassing global TLS.
private final class LANInspectionSessionDelegate: NSObject, URLSessionDelegate, @unchecked Sendable {
    private let lock = NSLock()
    private var _subject: String?

    var capturedSubject: String? {
        lock.lock()
        defer { lock.unlock() }
        return _subject
    }

    func urlSession(
        _ session: URLSession,
        didReceive challenge: URLAuthenticationChallenge,
        completionHandler: @escaping (URLSession.AuthChallengeDisposition, URLCredential?) -> Void
    ) {
        if challenge.protectionSpace.authenticationMethod == NSURLAuthenticationMethodServerTrust,
           let trust = challenge.protectionSpace.serverTrust
        {
            if let chain = SecTrustCopyCertificateChain(trust) as? [SecCertificate],
               let leaf = chain.first,
               let summary = SecCertificateCopySubjectSummary(leaf) as String?
            {
                lock.lock()
                _subject = summary
                lock.unlock()
            }
            completionHandler(.useCredential, URLCredential(trust: trust))
            return
        }
        completionHandler(.performDefaultHandling, nil)
    }
}

import Foundation
import Network

/// Targeted, low-noise TCP connect prober for high-signal ports on LAN hosts.
/// Focuses on proxy relays, exposed debug/remote-access ports, and basic HTTP/SSH fingerprinting.
enum PortProbeCollector {
    struct PortSpec: Equatable, Sendable {
        var port: UInt16
        var serviceName: String
        var isSuspicious: Bool
    }

    static let defaultSpecs: [PortSpec] = [
        PortSpec(port: 1080, serviceName: "SOCKS Proxy", isSuspicious: true),
        PortSpec(port: 3128, serviceName: "HTTP Proxy (Squid)", isSuspicious: true),
        PortSpec(port: 8080, serviceName: "HTTP Proxy / Alt-HTTP", isSuspicious: true),
        PortSpec(port: 8888, serviceName: "Proxy / Debug HTTP", isSuspicious: true),
        PortSpec(port: 9050, serviceName: "Tor SOCKS", isSuspicious: true),
        PortSpec(port: 5555, serviceName: "Android ADB", isSuspicious: true),
        PortSpec(port: 23, serviceName: "Telnet", isSuspicious: true),
        PortSpec(port: 5900, serviceName: "VNC", isSuspicious: true),
        PortSpec(port: 3389, serviceName: "RDP", isSuspicious: true),
        PortSpec(port: 22, serviceName: "SSH", isSuspicious: false),
        PortSpec(port: 80, serviceName: "HTTP", isSuspicious: false),
        PortSpec(port: 443, serviceName: "HTTPS", isSuspicious: false),
        PortSpec(port: 445, serviceName: "SMB", isSuspicious: false),
    ]

    /// Probes the curated port list against a single LAN host with short per-port timeouts.
    static func probeHost(
        ip: String,
        specs: [PortSpec] = defaultSpecs,
        timeoutSeconds: TimeInterval = 0.6
    ) async -> [OpenPort] {
        await withTaskGroup(of: OpenPort?.self) { group in
            for spec in specs {
                group.addTask {
                    let open = await isPortOpen(host: ip, port: spec.port, timeoutSeconds: timeoutSeconds)
                    guard open else { return nil }
                    return OpenPort(
                        port: spec.port,
                        serviceName: spec.serviceName,
                        isSuspicious: spec.isSuspicious
                    )
                }
            }
            var results: [OpenPort] = []
            for await item in group {
                if let item { results.append(item) }
            }
            return results.sorted { $0.port < $1.port }
        }
    }

    private static func isPortOpen(host: String, port: UInt16, timeoutSeconds: TimeInterval) async -> Bool {
        guard let nwPort = NWEndpoint.Port(rawValue: port) else { return false }
        let connection = NWConnection(host: NWEndpoint.Host(host), port: nwPort, using: .tcp)
        let queue = DispatchQueue(label: "io.github.imjasonh.lantern.probe.\(port)", qos: .utility)

        return await withCheckedContinuation { continuation in
            let lock = NSLock()
            var finished = false

            func finish(_ value: Bool) {
                lock.lock()
                defer { lock.unlock() }
                guard !finished else { return }
                finished = true
                connection.stateUpdateHandler = nil
                connection.cancel()
                continuation.resume(returning: value)
            }

            connection.stateUpdateHandler = { state in
                switch state {
                case .ready:
                    finish(true)
                case .failed, .cancelled:
                    finish(false)
                default:
                    break
                }
            }
            connection.start(queue: queue)

            queue.asyncAfter(deadline: .now() + timeoutSeconds) {
                finish(false)
            }
        }
    }
}

import Foundation

#if canImport(Darwin)
    import Darwin
#endif

/// The addresses this device is currently reachable at.
///
/// A URL is the whole point of running a server, and `127.0.0.1` is only
/// useful from Safari on the phone itself. Enumerating the interfaces is what
/// turns the experiment from "it is listening, apparently" into an address you
/// can type on a laptop.
enum LocalAddresses {
    struct Interface: Equatable {
        /// `en0` for Wi-Fi, `utun*` for a VPN or tailnet, `lo0` for loopback.
        var name: String
        var address: String

        var isLoopback: Bool { name.hasPrefix("lo") }
        /// A tailnet arrives as a utun interface, which is worth surfacing
        /// first once one exists.
        var isTunnel: Bool { name.hasPrefix("utun") || name.hasPrefix("tun") }

        /// Tailscale hands every node an address out of the CGNAT range
        /// 100.64.0.0/10, so a utun interface numbered in it is a tailnet and
        /// not some other VPN. Worth naming precisely: it is the one address
        /// here that works from anywhere in the world rather than only from
        /// this Wi-Fi.
        var isTailnet: Bool {
            guard isTunnel else { return false }
            let parts = address.split(separator: ".").compactMap { Int($0) }
            guard parts.count == 4, parts[0] == 100 else { return false }
            return (64...127).contains(parts[1])
        }

        var kind: String {
            if isLoopback { return "this device" }
            if isTailnet { return "tailnet — reachable anywhere" }
            if isTunnel { return "tunnel" }
            if name.hasPrefix("en") { return "Wi-Fi" }
            return name
        }
    }

    /// IPv4 addresses only. The point is a URL somebody will actually type,
    /// and a link-local IPv6 address with a scope suffix is not that.
    static func current() -> [Interface] {
        #if canImport(Darwin)
            var head: UnsafeMutablePointer<ifaddrs>?
            guard getifaddrs(&head) == 0, let first = head else { return [] }
            defer { freeifaddrs(head) }

            var found: [Interface] = []
            for entry in sequence(first: first, next: { $0.pointee.ifa_next }) {
                guard let rawAddress = entry.pointee.ifa_addr,
                    rawAddress.pointee.sa_family == UInt8(AF_INET),
                    entry.pointee.ifa_flags & UInt32(IFF_UP) != 0
                else { continue }

                var host = [CChar](repeating: 0, count: Int(NI_MAXHOST))
                let result = getnameinfo(
                    rawAddress, socklen_t(rawAddress.pointee.sa_len),
                    &host, socklen_t(host.count),
                    nil, 0, NI_NUMERICHOST
                )
                guard result == 0 else { continue }

                let name = String(cString: entry.pointee.ifa_name)
                let address = String(cString: host)
                guard !address.isEmpty else { continue }
                found.append(Interface(name: name, address: address))
            }
            return sorted(found)
        #else
            return []
        #endif
    }

    /// Most useful first: a tunnel if there is one, then the LAN, then
    /// loopback — which always works but only from this device.
    static func sorted(_ interfaces: [Interface]) -> [Interface] {
        interfaces.sorted { left, right in
            func rank(_ interface: Interface) -> Int {
                if interface.isTunnel { return 0 }
                if interface.isLoopback { return 2 }
                return 1
            }
            if rank(left) != rank(right) { return rank(left) < rank(right) }
            return left.name < right.name
        }
    }
}

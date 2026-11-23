import CoreWLAN
import Foundation
import SystemConfiguration

/// Collects the current network identity (SSID, default gateway IP/MAC, subnet, local IP).
enum NetworkIdentityCollector {
    static func collect() -> NetworkIdentity {
        let routeOut = (try? ProcessRunner.run("/sbin/route", arguments: ["-n", "get", "default"], timeoutSeconds: 4))?.stdout ?? ""
        let parsedRoute = parseDefaultRoute(routeOut)

        let ssid = CWWiFiClient.shared().interface()?.ssid()

        var gatewayMAC: String?
        if let gw = parsedRoute.gateway {
            let arpOut = (try? ProcessRunner.run("/usr/sbin/arp", arguments: ["-n", gw], timeoutSeconds: 4))?.stdout ?? ""
            gatewayMAC = parseSingleARPMAC(arpOut)
        }

        let localIP = parsedRoute.interface.flatMap { localIPv4Address(for: $0) }
        let subnetPrefix = (parsedRoute.gateway ?? localIP).flatMap { ipv4Prefix($0) }

        if parsedRoute.gateway == nil && parsedRoute.interface == nil && ssid == nil {
            return .offline
        }

        let id: String
        if let gwMAC = gatewayMAC {
            id = "gw:\(gwMAC)"
        } else if let gw = parsedRoute.gateway, let iface = parsedRoute.interface {
            id = "route:\(iface):\(gw)"
        } else if let ssid {
            id = "ssid:\(ssid)"
        } else {
            id = "iface:\(parsedRoute.interface ?? "unknown")"
        }

        return NetworkIdentity(
            id: id,
            ssid: ssid,
            gatewayIP: parsedRoute.gateway,
            gatewayMAC: gatewayMAC,
            localIP: localIP,
            interfaceName: parsedRoute.interface,
            subnetPrefix: subnetPrefix
        )
    }

    // MARK: - Pure parsers (unit-tested)

    static func parseDefaultRoute(_ stdout: String) -> (gateway: String?, interface: String?) {
        var gateway: String?
        var interface: String?
        for rawLine in stdout.split(separator: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            if line.hasPrefix("gateway:") {
                let value = line.dropFirst("gateway:".count).trimmingCharacters(in: .whitespaces)
                if !value.isEmpty { gateway = value }
            } else if line.hasPrefix("interface:") {
                let value = line.dropFirst("interface:".count).trimmingCharacters(in: .whitespaces)
                if !value.isEmpty { interface = value }
            }
        }
        return (gateway, interface)
    }

    static func parseSingleARPMAC(_ stdout: String) -> String? {
        // Example: "? (192.168.1.1) at aa:bb:cc:dd:ee:ff on en0 ifscope [ethernet]"
        for line in stdout.split(separator: "\n") {
            let tokens = line.split(separator: " ")
            if let atIndex = tokens.firstIndex(of: "at"), atIndex + 1 < tokens.count {
                let candidate = String(tokens[atIndex + 1])
                if candidate != "(incomplete)", let norm = OUILookup.normalizeMAC(candidate) {
                    return norm
                }
            }
        }
        return nil
    }

    static func ipv4Prefix(_ ip: String) -> String? {
        let parts = ip.split(separator: ".")
        guard parts.count == 4, parts.allSatisfy({ UInt8($0) != nil }) else { return nil }
        return parts.prefix(3).joined(separator: ".")
    }

    private static func localIPv4Address(for interfaceName: String) -> String? {
        var ifaddr: UnsafeMutablePointer<ifaddrs>?
        guard getifaddrs(&ifaddr) == 0, let first = ifaddr else { return nil }
        defer { freeifaddrs(ifaddr) }

        var ptr: UnsafeMutablePointer<ifaddrs>? = first
        while let current = ptr {
            let name = String(cString: current.pointee.ifa_name)
            if name == interfaceName,
               let addr = current.pointee.ifa_addr,
               addr.pointee.sa_family == UInt8(AF_INET)
            {
                var hostname = [CChar](repeating: 0, count: Int(NI_MAXHOST))
                if getnameinfo(
                    addr,
                    socklen_t(addr.pointee.sa_len),
                    &hostname,
                    socklen_t(hostname.count),
                    nil,
                    0,
                    NI_NUMERICHOST
                ) == 0 {
                    return String(cString: hostname)
                }
            }
            ptr = current.pointee.ifa_next
        }
        return nil
    }
}

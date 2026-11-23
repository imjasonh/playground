import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Narrow, zero-tool single-shot device classifier (<400 tokens).
/// Runs once per newly-discovered MAC and caches the result in `BaselineStore`.
enum DeviceClassifier {
    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    @Generable
    struct GeneratedClassification {
        @Guide(description: "Short human-friendly device label, 2–5 words (e.g. 'Apple TV', 'Brother Laser Printer', 'Generic Android Box')")
        var friendlyName: String

        @Guide(description: "One-word category: Router, Computer, Phone, TV, Speaker, Printer, IoT, Camera, Server, or Unknown")
        var category: String

        @Guide(description: "Optional brief security note if open ports or vendor look risky; empty string if normal")
        var riskNote: String
    }
    #endif

    /// Builds the compact prompt sent to AFM (exposed for unit tests asserting token budget).
    static func makePrompt(for device: LANDevice) -> String {
        var lines: [String] = [
            "Classify this local network device.",
            "IP: \(device.ipAddress)",
            "MAC vendor: \(device.vendor ?? "Unknown")",
        ]
        if let host = device.hostname, !host.isEmpty {
            lines.append("Hostname: \(host)")
        }
        if !device.mdnsServices.isEmpty {
            lines.append("mDNS: \(device.mdnsServices.prefix(6).joined(separator: ", "))")
        }
        if !device.openPorts.isEmpty {
            let ports = device.openPorts.prefix(8).map { "\($0.port)/\($0.serviceName)" }.joined(separator: ", ")
            lines.append("Open ports: \(ports)")
        }
        if device.isGateway {
            lines.append("Role: Default gateway router")
        }
        return lines.joined(separator: "\n")
    }

    static func classify(_ device: LANDevice) async -> DeviceClassification {
        #if canImport(FoundationModels)
        if #available(macOS 26.0, *), FoundationModelsAvailability.evaluate().isAvailable {
            let session = LanguageModelSession(
                instructions: """
                You label home-network devices from compact discovery facts. \
                Be accurate and concise. Never invent facts not in the input.
                """
            )
            if let response = try? await session.respond(
                to: makePrompt(for: device),
                generating: GeneratedClassification.self
            ) {
                let raw = response.content
                let name = raw.friendlyName.trimmingCharacters(in: .whitespacesAndNewlines)
                let cat = raw.category.trimmingCharacters(in: .whitespacesAndNewlines)
                let note = raw.riskNote.trimmingCharacters(in: .whitespacesAndNewlines)
                if !name.isEmpty {
                    return DeviceClassification(
                        friendlyName: name,
                        category: cat.isEmpty ? "Unknown" : cat,
                        riskNote: note.isEmpty ? nil : note,
                        source: .foundationModel
                    )
                }
            }
        }
        #endif
        return heuristicClassify(device)
    }

    /// Instant deterministic fallback (used on macOS 14–15 or when Apple Intelligence is off).
    static func heuristicClassify(_ device: LANDevice) -> DeviceClassification {
        let services = Set(device.mdnsServices.map { $0.lowercased() })
        let vendor = device.vendor ?? ""
        let lowerVendor = vendor.lowercased()
        let ports = Set(device.openPorts.map(\.port))

        var category = "Unknown"
        var name = device.hostname ?? (vendor.isEmpty ? "Unknown Device" : "\(vendor) Device")
        var riskNote: String?

        if device.isGateway {
            category = "Router"
            name = vendor.isEmpty ? "Home Router" : "\(vendor) Router"
        } else if device.isThisMac {
            category = "Computer"
            name = "This Mac"
        } else if services.contains(where: { $0.contains("_ipp") }) || lowerVendor.contains("brother") {
            category = "Printer"
            name = vendor.isEmpty ? "Network Printer" : "\(vendor) Printer"
        } else if services.contains(where: { $0.contains("_googlecast") }) || lowerVendor.contains("roku") {
            category = "TV"
            name = vendor.isEmpty ? "Streaming Device" : "\(vendor) Streaming"
        } else if lowerVendor.contains("sonos") || services.contains(where: { $0.contains("_raop") }) {
            category = "Speaker"
            name = vendor.isEmpty ? "AirPlay Speaker" : "\(vendor) Speaker"
        } else if lowerVendor.contains("espressif") || lowerVendor.contains("tuya") || lowerVendor.contains("hue") {
            category = "IoT"
            name = "\(vendor) Smart Device"
        } else if lowerVendor.contains("ring") || lowerVendor.contains("wyze") {
            category = "Camera"
            name = "\(vendor) Camera"
        } else if lowerVendor.contains("synology") || lowerVendor.contains("raspberry pi") {
            category = "Server"
            name = vendor
        } else if lowerVendor.contains("apple") {
            category = services.contains(where: { $0.contains("_airplay") }) ? "TV" : "Computer"
            name = device.hostname ?? "Apple Device"
        }

        if ports.contains(5555) {
            riskNote = "Exposes Android ADB (5555) on the LAN — common on unhardened Android TV boxes."
        } else if ports.contains(1080) || ports.contains(3128) || ports.contains(9050) {
            riskNote = "Exposes a proxy port on the local network."
        } else if ports.contains(23) {
            riskNote = "Exposes unencrypted Telnet (23)."
        }

        return DeviceClassification(
            friendlyName: name,
            category: category,
            riskNote: riskNote,
            source: .heuristic
        )
    }
}

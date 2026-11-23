import Foundation

/// Offline MAC OUI prefix → vendor lookup (zero network calls, instant).
/// Also detects locally-administered (randomized) MAC addresses (bit 1 of first octet).
enum OUILookup {
    /// Normalizes a MAC string (e.g. `a:b:c:d:e:f` or `AA-BB-CC-DD-EE-FF`) to `aa:bb:cc:dd:ee:ff`.
    static func normalizeMAC(_ raw: String) -> String? {
        let cleaned = raw
            .trimmingCharacters(in: .whitespacesAndNewlines)
            .replacingOccurrences(of: "-", with: ":")
            .lowercased()
        let parts = cleaned.split(separator: ":")
        guard parts.count == 6 else { return nil }
        var normalized: [String] = []
        normalized.reserveCapacity(6)
        for part in parts {
            guard part.count == 1 || part.count == 2,
                  let byte = UInt8(part, radix: 16)
            else { return nil }
            normalized.append(String(format: "%02x", byte))
        }
        return normalized.joined(separator: ":")
    }

    /// True if the MAC has the IEEE locally-administered bit set (common on iOS/macOS Private Wi-Fi).
    static func isLocallyAdministered(_ mac: String) -> Bool {
        guard let norm = normalizeMAC(mac),
              let firstByte = UInt8(norm.prefix(2), radix: 16)
        else { return false }
        return (firstByte & 0x02) != 0
    }

    static func vendor(for mac: String) -> String? {
        guard let norm = normalizeMAC(mac) else { return nil }
        let prefix = String(norm.prefix(8))
        if let known = table[prefix] {
            return known
        }
        if isLocallyAdministered(norm) {
            return "Private / Randomized MAC"
        }
        return nil
    }

    // Curated common home-network OUI prefixes (lowercase `xx:xx:xx`).
    private static let table: [String: String] = [
        // Apple
        "00:1c:b3": "Apple", "00:25:00": "Apple", "14:10:9f": "Apple",
        "28:cf:e9": "Apple", "3c:15:c2": "Apple", "40:b3:95": "Apple",
        "60:03:08": "Apple", "70:56:81": "Apple", "80:e6:50": "Apple",
        "a4:83:e7": "Apple", "ac:bc:32": "Apple", "bc:d0:74": "Apple",
        "d0:03:4b": "Apple", "dc:a9:04": "Apple", "f0:18:98": "Apple",
        // Ubiquiti / UniFi
        "04:18:d6": "Ubiquiti", "18:e8:29": "Ubiquiti", "24:5a:4c": "Ubiquiti",
        "44:d9:e7": "Ubiquiti", "68:d7:9a": "Ubiquiti", "74:83:c2": "Ubiquiti",
        "78:8a:20": "Ubiquiti", "80:2a:a8": "Ubiquiti", "b4:fb:e4": "Ubiquiti",
        "dc:9f:db": "Ubiquiti", "e0:63:da": "Ubiquiti", "f0:9f:c2": "Ubiquiti",
        // Raspberry Pi
        "28:cd:c1": "Raspberry Pi", "b8:27:eb": "Raspberry Pi",
        "d8:3a:dd": "Raspberry Pi", "dc:a6:32": "Raspberry Pi",
        "e4:5f:01": "Raspberry Pi",
        // Espressif (ESP32 / ESP8266 IoT)
        "24:0a:c4": "Espressif IoT", "30:ae:a4": "Espressif IoT",
        "3c:71:bf": "Espressif IoT", "40:f5:20": "Espressif IoT",
        "7c:9e:bd": "Espressif IoT", "84:cc:a8": "Espressif IoT",
        "a4:cf:12": "Espressif IoT", "c4:4f:33": "Espressif IoT",
        "cc:50:e3": "Espressif IoT", "ec:fa:bc": "Espressif IoT",
        // Google / Nest
        "18:b4:30": "Google / Nest", "30:fd:38": "Google",
        "44:07:0b": "Google", "54:60:09": "Google", "64:16:66": "Google / Nest",
        "a4:77:33": "Google", "d4:f5:47": "Google", "f4:f5:d8": "Google",
        // Amazon / Echo / Ring / Eero
        "00:fc:8b": "Amazon", "18:74:2e": "Amazon", "34:d2:70": "Amazon",
        "44:65:0d": "Amazon", "50:dc:e7": "Amazon", "68:37:e9": "Amazon",
        "74:c2:46": "Amazon", "84:d6:d0": "Amazon", "ac:63:be": "Amazon",
        "fc:65:de": "Amazon", "0c:47:c9": "Amazon",
        "34:3e:a4": "Ring", "54:e0:19": "Ring",
        "70:b3:d5": "Eero", "e8:9f:80": "Eero",
        // Sonos
        "00:0e:58": "Sonos", "34:7e:5c": "Sonos", "48:a6:b8": "Sonos",
        "5c:aa:fd": "Sonos", "78:28:ca": "Sonos", "94:9f:3e": "Sonos",
        "b8:e9:37": "Sonos",
        // Roku / Samsung / LG / Sony
        "08:05:81": "Roku", "ac:3a:7a": "Roku", "b0:a7:37": "Roku",
        "cc:6d:a0": "Roku", "d8:31:34": "Roku",
        "00:12:fb": "Samsung", "34:23:ba": "Samsung", "50:01:bb": "Samsung",
        "84:25:db": "Samsung", "cc:07:ab": "Samsung",
        "00:e0:91": "LG", "38:8c:50": "LG", "a8:23:fe": "LG",
        "00:1d:ba": "Sony", "30:f9:ed": "Sony", "ac:9b:0a": "Sony",
        // Routers & switches: TP-Link, Netgear, ASUS, Linksys, Synology
        "14:cc:20": "TP-Link", "50:c7:bf": "TP-Link", "60:32:b1": "TP-Link",
        "98:da:c4": "TP-Link", "b0:be:76": "TP-Link", "c0:06:c3": "TP-Link",
        "00:14:6c": "Netgear", "20:e5:2a": "Netgear", "a0:40:a0": "Netgear",
        "04:92:26": "ASUS", "1c:87:2c": "ASUS", "2c:fd:a1": "ASUS",
        "00:11:32": "Synology", "90:09:d0": "Synology",
        // Printers & smart home
        "00:1b:a9": "Brother", "30:05:5c": "Brother",
        "00:17:88": "Philips Hue", "ec:b5:fa": "Philips Hue",
        "10:d5:61": "Tuya / SmartLife", "d8:f1:5b": "Tuya / SmartLife",
        "7c:2f:80": "Wyze", "2c:aa:8e": "Wyze",
        // Common chipsets (often cheap Android TV boxes / IoT)
        "00:e0:4c": "Realtek", "52:54:00": "QEMU / Virtual",
        "08:00:27": "VirtualBox", "00:0c:29": "VMware",
    ]
}

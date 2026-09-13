import Foundation

/// A command the iPhone writes to the ESP32 command characteristic.
enum ESP32BLECommand: Equatable {
    case ledOn
    case ledOff
    case blink(periodMs: UInt32)
    case stop
}

/// Latest device status, parsed from a notify payload.
struct ESP32BLEStatus: Equatable {
    var ledOn: Bool
    var blinkMs: UInt32
    var uptimeS: UInt32
    var heapFree: UInt32?
    var lastCommand: String
}

/// Shared wire format with `esp32-ble/src/protocol.rs`.
enum ESP32BLEProtocol {
    static let deviceName = "PlaygroundBLE"
    static let serviceUUIDString = "4FAFC201-1FB5-459E-8FCC-C5C9C331914B"
    static let commandUUIDString = "BEB5483E-36E1-4688-B7F5-EA07361B26A6"
    static let statusUUIDString = "1A3C0001-36E1-4688-B7F5-EA07361B26A6"

    static let minBlinkMs: UInt32 = 50
    static let maxBlinkMs: UInt32 = 60_000

    /// Parse a command written to the command characteristic.
    static func parseCommand(_ raw: String) -> ESP32BLECommand? {
        let parts = raw.split(whereSeparator: \.isWhitespace).map(String.init)
        guard let head = parts.first?.lowercased() else {
            return nil
        }
        switch head {
        case "on":
            return .ledOn
        case "off":
            return .ledOff
        case "stop" where parts.count == 1:
            return .stop
        case "led" where parts.count == 2:
            switch parts[1].lowercased() {
            case "on":
                return .ledOn
            case "off":
                return .ledOff
            default:
                return nil
            }
        case "blink":
            return parseBlink(Array(parts.dropFirst()))
        default:
            return nil
        }
    }

    /// Canonical command text written by the iOS presets.
    static func encode(_ command: ESP32BLECommand) -> String {
        switch command {
        case .ledOn:
            return "led on"
        case .ledOff:
            return "led off"
        case .stop:
            return "stop"
        case .blink(let periodMs):
            return "blink \(formatSeconds(periodMs))"
        }
    }

    /// Encode a status line (used by tests; the firmware is the producer).
    static func formatStatus(_ status: ESP32BLEStatus) -> String {
        let led = status.ledOn ? "on" : "off"
        if let heap = status.heapFree {
            return "led=\(led) blink_ms=\(status.blinkMs) uptime_s=\(status.uptimeS) heap=\(heap) last=\(status.lastCommand)"
        }
        return "led=\(led) blink_ms=\(status.blinkMs) uptime_s=\(status.uptimeS) last=\(status.lastCommand)"
    }

    /// Parse a status line from the notify characteristic.
    static func parseStatus(_ raw: String) -> ESP32BLEStatus? {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed.isEmpty {
            return nil
        }
        let prefix: String
        let lastCommand: String
        if let range = trimmed.range(of: " last=") {
            prefix = String(trimmed[..<range.lowerBound])
            lastCommand = String(trimmed[range.upperBound...])
        } else {
            prefix = trimmed
            lastCommand = ""
        }
        var ledOn: Bool?
        var blinkMs: UInt32?
        var uptimeS: UInt32?
        var heapFree: UInt32?
        for part in prefix.split(whereSeparator: \.isWhitespace).map(String.init) {
            if let value = part.stripPrefix("led=") {
                ledOn = value == "on"
            } else if let value = part.stripPrefix("blink_ms=") {
                guard let parsed = UInt32(value) else {
                    return nil
                }
                blinkMs = parsed
            } else if let value = part.stripPrefix("uptime_s=") {
                guard let parsed = UInt32(value) else {
                    return nil
                }
                uptimeS = parsed
            } else if let value = part.stripPrefix("heap=") {
                guard let parsed = UInt32(value) else {
                    return nil
                }
                heapFree = parsed
            }
        }
        guard let ledOn, let blinkMs, let uptimeS else {
            return nil
        }
        return ESP32BLEStatus(
            ledOn: ledOn,
            blinkMs: blinkMs,
            uptimeS: uptimeS,
            heapFree: heapFree,
            lastCommand: lastCommand
        )
    }

    private static func parseBlink(_ args: [String]) -> ESP32BLECommand? {
        var tokens = args.map { $0.lowercased() }
        if tokens.first == "every" {
            tokens.removeFirst()
        }
        guard tokens.count == 1, let periodMs = parsePeriod(tokens[0]) else {
            return nil
        }
        guard periodMs >= minBlinkMs, periodMs <= maxBlinkMs else {
            return nil
        }
        return .blink(periodMs: periodMs)
    }

    private static func parsePeriod(_ token: String) -> UInt32? {
        if let ms = token.stripSuffix("ms") {
            guard !ms.isEmpty, ms.allSatisfy(\.isNumber) else {
                return nil
            }
            return UInt32(ms)
        }
        let secs = token.stripSuffix("s") ?? token
        return parseSeconds(secs)
    }

    private static func parseSeconds(_ text: String) -> UInt32? {
        if let dot = text.firstIndex(of: ".") {
            let wholeS = String(text[..<dot])
            let fracS = String(text[text.index(after: dot)...])
            guard !wholeS.isEmpty, wholeS.allSatisfy(\.isNumber) else {
                return nil
            }
            guard !fracS.isEmpty, fracS.allSatisfy(\.isNumber) else {
                return nil
            }
            guard let whole = UInt32(wholeS) else {
                return nil
            }
            var frac = String(fracS.prefix(3))
            while frac.count < 3 {
                frac.append("0")
            }
            guard let fracMs = UInt32(frac) else {
                return nil
            }
            return whole.multipliedReportingOverflow(by: 1000).overflow
                ? nil
                : whole * 1000 + fracMs
        }
        guard !text.isEmpty, text.allSatisfy(\.isNumber), let whole = UInt32(text) else {
            return nil
        }
        return whole.multipliedReportingOverflow(by: 1000).overflow ? nil : whole * 1000
    }

    private static func formatSeconds(_ periodMs: UInt32) -> String {
        let whole = periodMs / 1000
        let frac = periodMs % 1000
        if frac == 0 {
            return String(whole)
        }
        var fracS = String(format: "%03u", frac)
        while fracS.last == "0" {
            fracS.removeLast()
        }
        return "\(whole).\(fracS)"
    }
}

private extension String {
    func stripPrefix(_ prefix: String) -> String? {
        guard hasPrefix(prefix) else {
            return nil
        }
        return String(dropFirst(prefix.count))
    }

    func stripSuffix(_ suffix: String) -> String? {
        guard hasSuffix(suffix) else {
            return nil
        }
        return String(dropLast(suffix.count))
    }
}

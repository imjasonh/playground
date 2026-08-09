import Foundation

/// A bearer token plus the instant it stops being accepted.
struct GCPAuthToken: Equatable {
    let value: String
    let expiresAt: Date

    /// Treat a token as spent slightly before its real expiry so a request that
    /// leaves the device just under the wire doesn't arrive just over it.
    static let refreshSkew: TimeInterval = 60

    func isValid(at now: Date) -> Bool {
        now.addingTimeInterval(Self.refreshSkew) < expiresAt
    }

    /// Short prefix for display. Whole tokens are never worth putting on screen.
    var redacted: String {
        let head = value.prefix(12)
        return value.count > 12 ? "\(head)… (\(value.count) chars)" : String(head)
    }
}

/// The result of signing in to Firebase Auth.
struct GCPAuthIdentity: Equatable {
    let idToken: GCPAuthToken
    let refreshToken: String
    let userID: String
    let provider: Provider

    enum Provider: String, Equatable {
        case anonymous
        case apple

        var label: String {
            switch self {
            case .anonymous: return "Anonymous"
            case .apple: return "Sign in with Apple"
            }
        }
    }
}

enum GCPAuthError: Error, Equatable, LocalizedError {
    case notConfigured
    case appAttestUnsupported
    case appleSignInDisabled
    case appleSignInCancelled
    case appleSignInFailed(String)
    case missingAppleIdentityToken
    case badURL(String)
    case malformedResponse(String)
    case http(status: Int, message: String)

    var errorDescription: String? {
        switch self {
        case .notConfigured:
            return "No Firebase project is configured."
        case .appAttestUnsupported:
            return "App Attest is not available on this device."
        case .appleSignInDisabled:
            return "Sign in with Apple is turned off in this build."
        case .appleSignInCancelled:
            return "Sign in with Apple was cancelled."
        case .appleSignInFailed(let message):
            return "Sign in with Apple failed: \(message)"
        case .missingAppleIdentityToken:
            return "Apple returned no identity token."
        case .badURL(let string):
            return "Could not build a URL from \(string)."
        case .malformedResponse(let detail):
            return detail
        case .http(let status, let message):
            return message.isEmpty ? "HTTP \(status)" : "HTTP \(status): \(message)"
        }
    }
}

/// Google APIs express durations as a decimal number of seconds with a trailing
/// `s` (`"3600s"`), which `TimeInterval(_:)` will not parse on its own.
enum GCPAuthDuration {
    static func seconds(from string: String) -> TimeInterval? {
        let trimmed = string.trimmingCharacters(in: .whitespaces)
        let digits = trimmed.hasSuffix("s") ? String(trimmed.dropLast()) : trimmed
        return TimeInterval(digits)
    }
}

/// RFC 3339 timestamps, with and without fractional seconds — the IAM
/// Credentials API uses the former and other Google APIs use the latter.
enum GCPAuthTimestamp {
    static func date(from string: String) -> Date? {
        let withFraction = ISO8601DateFormatter()
        withFraction.formatOptions = [.withInternetDateTime, .withFractionalSeconds]
        if let date = withFraction.date(from: string) { return date }
        let plain = ISO8601DateFormatter()
        plain.formatOptions = [.withInternetDateTime]
        return plain.date(from: string)
    }
}

/// Google's JSON `bytes` fields are base64, but whether they arrive standard or
/// URL-safe (and padded or not) varies by endpoint, so decoding accepts all four
/// combinations while encoding always emits the standard alphabet.
enum GCPAuthBase64 {
    static func encode(_ data: Data) -> String {
        data.base64EncodedString()
    }

    /// JWT segments use the URL-safe alphabet with the padding stripped.
    static func encodeURLSafe(_ data: Data) -> String {
        data.base64EncodedString()
            .replacingOccurrences(of: "+", with: "-")
            .replacingOccurrences(of: "/", with: "_")
            .replacingOccurrences(of: "=", with: "")
    }

    static func decode(_ string: String) -> Data? {
        var normalized = string
            .replacingOccurrences(of: "-", with: "+")
            .replacingOccurrences(of: "_", with: "/")
        let remainder = normalized.count % 4
        if remainder > 0 {
            normalized.append(String(repeating: "=", count: 4 - remainder))
        }
        return Data(base64Encoded: normalized)
    }
}

/// `application/x-www-form-urlencoded` bodies, which is what Google's STS
/// endpoint and the Secure Token refresh endpoint expect.
enum GCPAuthForm {
    static let unreserved: CharacterSet = {
        var set = CharacterSet.alphanumerics
        set.insert(charactersIn: "-._~")
        return set
    }()

    static func percentEncode(_ value: String) -> String {
        value.addingPercentEncoding(withAllowedCharacters: unreserved) ?? value
    }

    static func body(_ fields: [(String, String)]) -> Data {
        let joined = fields
            .map { "\(percentEncode($0.0))=\(percentEncode($0.1))" }
            .joined(separator: "&")
        return Data(joined.utf8)
    }
}

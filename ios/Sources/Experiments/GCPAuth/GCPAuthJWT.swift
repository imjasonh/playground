import Foundation

/// Reads the claims out of a JWT **without verifying it**.
///
/// This exists so the experiment can show what each token in the chain actually
/// says. Nothing here is a security check: signature verification belongs on the
/// server that consumes the token, against the issuer's published JWKS. A client
/// inspecting a token it was just handed learns nothing it can trust.
enum GCPAuthJWT {
    struct Claim: Equatable, Identifiable {
        let name: String
        let value: String

        var id: String { name }
    }

    struct Claims: Equatable {
        let issuer: String?
        let subject: String?
        let audience: String?
        let issuedAt: Date?
        let expiresAt: Date?
        /// Every claim, flattened to strings and sorted by name, for display.
        let all: [Claim]
    }

    static func decode(_ token: String) -> Claims? {
        let segments = token.split(separator: ".", omittingEmptySubsequences: false)
        guard segments.count == 3 else { return nil }
        guard let payload = GCPAuthBase64.decode(String(segments[1])) else { return nil }
        guard let object = try? JSONSerialization.jsonObject(with: payload),
              let claims = object as? [String: Any] else {
            return nil
        }

        return Claims(
            issuer: claims["iss"] as? String,
            subject: claims["sub"] as? String,
            audience: audience(from: claims["aud"]),
            issuedAt: epoch(claims["iat"]),
            expiresAt: epoch(claims["exp"]),
            all: claims.keys.sorted().map { Claim(name: $0, value: display(claims[$0])) }
        )
    }

    /// `aud` is a single string on Firebase ID tokens, but the spec allows an array.
    private static func audience(from value: Any?) -> String? {
        if let single = value as? String { return single }
        if let many = value as? [String] { return many.joined(separator: ", ") }
        return nil
    }

    private static func epoch(_ value: Any?) -> Date? {
        guard let number = value as? NSNumber else { return nil }
        return Date(timeIntervalSince1970: number.doubleValue)
    }

    private static func display(_ value: Any?) -> String {
        guard let value, !(value is NSNull) else { return "null" }
        if let string = value as? String { return string }
        if let number = value as? NSNumber { return number.stringValue }
        if let array = value as? [Any] {
            return array.map { display($0) }.joined(separator: ", ")
        }
        if let dictionary = value as? [String: Any] {
            return dictionary.keys.sorted()
                .map { "\($0)=\(display(dictionary[$0]))" }
                .joined(separator: " ")
        }
        return String(describing: value)
    }
}

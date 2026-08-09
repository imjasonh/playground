import CryptoKit
import Foundation

/// `sha256:<hex>` content digests, the identity of every blob we pull.
///
/// Everything the app writes to disk is verified against the digest the
/// registry advertised, so a corrupt or substituted layer never reaches the
/// runtime.
enum OCIDigest {
    static func sha256(of data: Data) -> String {
        let hash = CryptoKit.SHA256.hash(data: data)
        let hex = hash.map { String(format: "%02x", $0) }.joined()
        return "sha256:\(hex)"
    }

    static func isValid(_ digest: String) -> Bool {
        guard digest.hasPrefix("sha256:") else { return false }
        let hex = digest.dropFirst("sha256:".count)
        guard hex.count == 64 else { return false }
        return hex.allSatisfy { $0.isHexDigit && ($0.isNumber || $0.isLowercase) }
    }

    /// The hex portion, which is also the on-disk filename in an OCI layout.
    static func hex(_ digest: String) -> String? {
        guard isValid(digest) else { return nil }
        return String(digest.dropFirst("sha256:".count))
    }

    static func verify(_ data: Data, matches digest: String) throws {
        let actual = sha256(of: data)
        guard actual == digest else {
            throw OCIDigestError.mismatch(expected: digest, actual: actual)
        }
    }
}

enum OCIDigestError: Error, Equatable, LocalizedError {
    case mismatch(expected: String, actual: String)

    var errorDescription: String? {
        switch self {
        case .mismatch(let expected, let actual):
            return "Digest mismatch — expected \(expected), got \(actual)"
        }
    }
}

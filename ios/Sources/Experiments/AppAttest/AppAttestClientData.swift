import CryptoKit
import Foundation

/// JSON block hashed and sent to `attestKey` / the Worker.
///
/// Keys are encoded in sorted order so the bytes the app hashes are the same
/// bytes the Worker re-hashes.
struct AppAttestClientData: Codable, Equatable {
    var challenge: String
    var userId: String
    var deviceId: String

    /// Compact JSON used as `clientDataHash` input and posted as a string.
    func jsonBytes() throws -> Data {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.sortedKeys]
        return try encoder.encode(self)
    }
}

enum AppAttestHashing {
    /// SHA-256 digest passed to `DCAppAttestService.attestKey`.
    static func sha256(_ data: Data) -> Data {
        Data(SHA256.hash(data: data))
    }
}

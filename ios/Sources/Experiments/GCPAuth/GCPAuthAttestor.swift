import CryptoKit
import DeviceCheck
import Foundation

/// The slice of `DCAppAttestService` the credential chain needs.
///
/// Behind the protocol so the flow can run in the Simulator and in tests, where
/// App Attest does not exist.
protocol GCPAuthAttestor {
    var isSupported: Bool { get }
    func generateKey() async throws -> String
    func attestKey(_ keyID: String, clientDataHash: Data) async throws -> Data
    func generateAssertion(_ keyID: String, clientDataHash: Data) async throws -> Data
}

/// The real thing: a P-256 keypair generated inside the Secure Enclave, whose
/// private half is not extractable even by this app. `attestKey` asks Apple to
/// certify that the key belongs to a genuine, correctly signed install of this
/// bundle id on genuine Apple hardware; the server verifies that certificate
/// chain before it trusts anything the key later signs.
struct GCPAuthDeviceCheckAttestor: GCPAuthAttestor {
    private var service: DCAppAttestService { .shared }

    var isSupported: Bool { service.isSupported }

    func generateKey() async throws -> String {
        try await withCheckedThrowingContinuation { continuation in
            service.generateKey { keyID, error in
                if let error {
                    continuation.resume(throwing: error)
                } else if let keyID {
                    continuation.resume(returning: keyID)
                } else {
                    continuation.resume(
                        throwing: GCPAuthError.malformedResponse("App Attest returned no key id.")
                    )
                }
            }
        }
    }

    func attestKey(_ keyID: String, clientDataHash: Data) async throws -> Data {
        try await withCheckedThrowingContinuation { continuation in
            service.attestKey(keyID, clientDataHash: clientDataHash) { attestation, error in
                if let error {
                    continuation.resume(throwing: error)
                } else if let attestation {
                    continuation.resume(returning: attestation)
                } else {
                    continuation.resume(
                        throwing: GCPAuthError.malformedResponse("App Attest returned no attestation.")
                    )
                }
            }
        }
    }

    func generateAssertion(_ keyID: String, clientDataHash: Data) async throws -> Data {
        try await withCheckedThrowingContinuation { continuation in
            service.generateAssertion(keyID, clientDataHash: clientDataHash) { assertion, error in
                if let error {
                    continuation.resume(throwing: error)
                } else if let assertion {
                    continuation.resume(returning: assertion)
                } else {
                    continuation.resume(
                        throwing: GCPAuthError.malformedResponse("App Attest returned no assertion.")
                    )
                }
            }
        }
    }
}

/// Stands in for the Secure Enclave where there isn't one.
///
/// It produces well-formed but meaningless bytes. A server that actually
/// verifies them will reject them, which is exactly right: the simulated path
/// exists to walk the flow, never to pass it.
final class GCPAuthSimulatedAttestor: GCPAuthAttestor {
    private(set) var generatedKeyCount = 0
    private(set) var attestedHashes: [Data] = []
    private(set) var assertedHashes: [Data] = []

    let isSupported = false

    func generateKey() async throws -> String {
        generatedKeyCount += 1
        return "simulated-key-\(generatedKeyCount)"
    }

    func attestKey(_ keyID: String, clientDataHash: Data) async throws -> Data {
        attestedHashes.append(clientDataHash)
        return Data("simulated-attestation:\(keyID)".utf8) + clientDataHash
    }

    func generateAssertion(_ keyID: String, clientDataHash: Data) async throws -> Data {
        assertedHashes.append(clientDataHash)
        return Data("simulated-assertion:\(keyID)".utf8) + clientDataHash
    }
}

enum GCPAuthClientData {
    /// App Attest signs a hash of whatever the caller says the request is about.
    /// For the first exchange that is the challenge Firebase just issued, which
    /// is what stops an attestation being captured and replayed.
    static func attestationHash(challenge: Data) -> Data {
        Data(SHA256.hash(data: challenge))
    }

    /// Later assertions hash the artifact together with a fresh challenge: the
    /// artifact ties the assertion back to the key that was already attested,
    /// and the challenge makes each one single-use. This mirrors what the
    /// Firebase App Check SDK signs, and the server recomputes it the same way.
    static func assertionHash(artifact: Data, challenge: Data) -> Data {
        Data(SHA256.hash(data: artifact + challenge))
    }
}

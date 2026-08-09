import Foundation

/// Firebase App Check, driven over its REST API rather than the Firebase SDK.
///
/// Three calls: ask for a challenge, trade an App Attest attestation for an
/// artifact plus a token, then trade cheap assertions for tokens from then on.
/// The App Check token that comes back is a JWT signed by Google, so any backend
/// can verify it against `firebaseappcheck.googleapis.com/v1/jwks` without
/// talking to Apple at all.
struct GCPAuthAppCheckClient {
    let configuration: GCPAuthConfiguration
    let http: GCPAuthHTTPClient

    private static let host = "firebaseappcheck.googleapis.com"

    func generateChallenge() async throws -> Data {
        let endpoint = try url(method: "generateAppAttestChallenge")
        let response: ChallengeResponse = try await http.postJSON(url: endpoint, body: EmptyBody())
        guard let challenge = GCPAuthBase64.decode(response.challenge) else {
            throw GCPAuthError.malformedResponse("App Check challenge was not base64.")
        }
        return challenge
    }

    func exchangeAttestation(
        keyID: String,
        attestation: Data,
        challenge: Data
    ) async throws -> (artifact: Data, token: GCPAuthToken) {
        let endpoint = try url(method: "exchangeAppAttestAttestation")
        let response: AttestationResponse = try await http.postJSON(
            url: endpoint,
            body: AttestationRequest(
                attestationStatement: GCPAuthBase64.encode(attestation),
                challenge: GCPAuthBase64.encode(challenge),
                keyId: keyID
            )
        )
        guard let artifact = GCPAuthBase64.decode(response.artifact) else {
            throw GCPAuthError.malformedResponse("App Check artifact was not base64.")
        }
        let issued = try token(from: response.appCheckToken)
        return (artifact, issued)
    }

    func exchangeAssertion(
        artifact: Data,
        assertion: Data,
        challenge: Data
    ) async throws -> GCPAuthToken {
        let endpoint = try url(method: "exchangeAppAttestAssertion")
        let response: TokenResponse = try await http.postJSON(
            url: endpoint,
            body: AssertionRequest(
                artifact: GCPAuthBase64.encode(artifact),
                assertion: GCPAuthBase64.encode(assertion),
                challenge: GCPAuthBase64.encode(challenge)
            )
        )
        return try token(from: response)
    }

    private func url(method: String) throws -> URL {
        try GCPAuthURLBuilder.googleAPI(
            host: Self.host,
            path: "v1/\(configuration.appCheckResource):\(method)",
            apiKey: configuration.apiKey
        )
    }

    private func token(from response: TokenResponse, now: Date = Date()) throws -> GCPAuthToken {
        guard let seconds = GCPAuthDuration.seconds(from: response.ttl) else {
            throw GCPAuthError.malformedResponse("App Check ttl '\(response.ttl)' was not a duration.")
        }
        return GCPAuthToken(value: response.token, expiresAt: now.addingTimeInterval(seconds))
    }

    private struct EmptyBody: Encodable {}

    private struct AttestationRequest: Encodable {
        let attestationStatement: String
        let challenge: String
        let keyId: String
    }

    private struct AssertionRequest: Encodable {
        let artifact: String
        let assertion: String
        let challenge: String
    }

    private struct ChallengeResponse: Decodable {
        let challenge: String
        let ttl: String?
    }

    private struct TokenResponse: Decodable {
        let token: String
        let ttl: String
    }

    private struct AttestationResponse: Decodable {
        let artifact: String
        let appCheckToken: TokenResponse
    }
}

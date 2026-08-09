import Foundation

/// Answers the whole credential chain in-process, so the experiment demonstrates
/// the flow with no Firebase project, no network, and no Secure Enclave.
///
/// The tokens it mints are structurally real JWTs and structurally wrong
/// everything else: the signature segment is a literal string. That is
/// deliberate — anything that actually verified them would reject them, so there
/// is no way to mistake this path for authentication.
final class GCPAuthSimulatedTransport: GCPAuthTransport {
    let configuration: GCPAuthConfiguration
    /// Small artificial delay so the UI's step-by-step progress is legible.
    let latency: TimeInterval

    private(set) var requestedPaths: [String] = []
    private var challengeCount = 0
    private var issuedTokenCount = 0

    init(configuration: GCPAuthConfiguration, latency: TimeInterval = 0) {
        self.configuration = configuration
        self.latency = latency
    }

    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse) {
        guard let url = request.url else {
            throw GCPAuthError.badURL("<no url>")
        }
        if latency > 0 {
            try await Task.sleep(nanoseconds: UInt64(latency * 1_000_000_000))
        }

        let path = url.path
        requestedPaths.append(path)
        let body = try respond(to: path, host: url.host ?? "")
        let data = try JSONSerialization.data(withJSONObject: body)
        let response = HTTPURLResponse(
            url: url,
            statusCode: 200,
            httpVersion: "HTTP/1.1",
            headerFields: ["Content-Type": "application/json"]
        )
        guard let response else {
            throw GCPAuthError.malformedResponse("Could not build a simulated response.")
        }
        return (data, response)
    }

    private func respond(to path: String, host: String) throws -> [String: Any] {
        if path.hasSuffix(":generateAppAttestChallenge") {
            challengeCount += 1
            let challenge = Data("simulated-challenge-\(challengeCount)".utf8)
            return ["challenge": GCPAuthBase64.encode(challenge), "ttl": "60s"]
        }

        if path.hasSuffix(":exchangeAppAttestAttestation") {
            return [
                "artifact": GCPAuthBase64.encode(Data("simulated-artifact".utf8)),
                "appCheckToken": ["token": appCheckJWT(), "ttl": "3600s"]
            ]
        }

        if path.hasSuffix(":exchangeAppAttestAssertion") {
            return ["token": appCheckJWT(), "ttl": "3600s"]
        }

        if path.hasSuffix("accounts:signUp") || path.hasSuffix("accounts:signInWithIdp") {
            let provider = path.hasSuffix("accounts:signUp") ? "anonymous" : "apple.com"
            return [
                "idToken": firebaseJWT(signInProvider: provider),
                "refreshToken": "simulated-refresh-token",
                "expiresIn": "3600",
                "localId": Self.simulatedUserID
            ]
        }

        if host == "securetoken.googleapis.com" {
            return [
                "id_token": firebaseJWT(signInProvider: "anonymous"),
                "refresh_token": "simulated-refresh-token",
                "expires_in": "3600",
                "user_id": Self.simulatedUserID
            ]
        }

        if host == "sts.googleapis.com" {
            issuedTokenCount += 1
            return [
                "access_token": "ya29.simulated-federated-token-\(issuedTokenCount)",
                "issued_token_type": "urn:ietf:params:oauth:token-type:access_token",
                "token_type": "Bearer",
                "expires_in": 3600
            ]
        }

        if path.hasSuffix(":generateAccessToken") {
            issuedTokenCount += 1
            let expiry = Date().addingTimeInterval(3600)
            let formatter = ISO8601DateFormatter()
            formatter.formatOptions = [.withInternetDateTime]
            return [
                "accessToken": "ya29.simulated-impersonated-token-\(issuedTokenCount)",
                "expireTime": formatter.string(from: expiry)
            ]
        }

        throw GCPAuthError.http(status: 404, message: "No simulated handler for \(path)")
    }

    private static let simulatedUserID = "simulated-user-0001"

    /// What Firebase's App Check service would sign: audience is the project,
    /// subject is the Firebase App ID, and `app_id` is what a backend keys off
    /// after verifying the signature against Google's JWKS.
    private func appCheckJWT() -> String {
        Self.unsignedJWT([
            "iss": "https://firebaseappcheck.googleapis.com/\(configuration.projectNumber)",
            "sub": configuration.appID,
            "aud": ["projects/\(configuration.projectNumber)", "projects/\(configuration.projectID)"],
            "app_id": configuration.appID,
            "iat": Int(Date().timeIntervalSince1970),
            "exp": Int(Date().addingTimeInterval(3600).timeIntervalSince1970)
        ])
    }

    /// What Firebase Auth would sign. The workload identity provider is created
    /// with exactly this `iss`, and `aud` has to equal the project id.
    private func firebaseJWT(signInProvider: String) -> String {
        Self.unsignedJWT([
            "iss": configuration.firebaseIssuer,
            "aud": configuration.projectID,
            "sub": Self.simulatedUserID,
            "user_id": Self.simulatedUserID,
            "auth_time": Int(Date().timeIntervalSince1970),
            "iat": Int(Date().timeIntervalSince1970),
            "exp": Int(Date().addingTimeInterval(3600).timeIntervalSince1970),
            "firebase": [
                "identities": [String: Any](),
                "sign_in_provider": signInProvider
            ]
        ])
    }

    static func unsignedJWT(_ claims: [String: Any]) -> String {
        let header: [String: Any] = ["alg": "none", "typ": "JWT", "kid": "simulated"]
        let headerData = (try? JSONSerialization.data(withJSONObject: header)) ?? Data()
        let claimsData = (try? JSONSerialization.data(withJSONObject: claims)) ?? Data()
        return [
            GCPAuthBase64.encodeURLSafe(headerData),
            GCPAuthBase64.encodeURLSafe(claimsData),
            GCPAuthBase64.encodeURLSafe(Data("simulated-not-a-real-signature".utf8))
        ].joined(separator: ".")
    }
}

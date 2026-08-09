import Foundation

/// Workload Identity Federation: trade a Firebase ID token for a real, short-lived
/// Google access token.
///
/// The pool provider is configured with Firebase's issuer, so Google's STS
/// verifies the ID token's signature against `securetoken.google.com`'s JWKS and
/// then maps its claims onto a Google principal. Nothing long-lived crosses the
/// wire in either direction, and no service account key exists to be stolen.
///
/// One honest caveat, spelled out in `docs/ios-gcp-auth-design.md`: **STS does
/// not look at App Check.** Attestation is enforced by Firebase Auth (and by
/// your own backend), not by this exchange. A client that already holds a valid
/// Firebase ID token can federate with it regardless of how it was obtained.
struct GCPAuthWorkloadIdentityClient {
    let configuration: GCPAuthConfiguration
    let http: GCPAuthHTTPClient

    private static let stsHost = "sts.googleapis.com"
    private static let iamCredentialsHost = "iamcredentials.googleapis.com"

    func federate(firebaseIDToken: String) async throws -> GCPAuthToken {
        let endpoint = try GCPAuthURLBuilder.googleAPI(host: Self.stsHost, path: "v1/token")
        let response: STSResponse = try await http.postForm(
            url: endpoint,
            fields: [
                ("audience", configuration.workloadIdentityAudience),
                ("grant_type", "urn:ietf:params:oauth:grant-type:token-exchange"),
                ("requested_token_type", "urn:ietf:params:oauth:token-type:access_token"),
                ("scope", configuration.scopeString),
                ("subject_token_type", "urn:ietf:params:oauth:token-type:jwt"),
                ("subject_token", firebaseIDToken)
            ]
        )
        return GCPAuthToken(
            value: response.accessToken,
            expiresAt: Date().addingTimeInterval(response.expiresIn)
        )
    }

    /// Optional second hop: the federated principal borrows a service account.
    ///
    /// Worth doing only when the app needs permissions you'd rather not grant to
    /// the whole pool. The service account must name the pool principal in a
    /// `roles/iam.workloadIdentityUser` binding, and it should be a purpose-built
    /// account with the narrowest role that works — impersonation hands the
    /// client everything that account can do for the lifetime of the token.
    func impersonate(serviceAccountEmail: String, federatedToken: String) async throws -> GCPAuthToken {
        let endpoint = try GCPAuthURLBuilder.googleAPI(
            host: Self.iamCredentialsHost,
            path: "v1/projects/-/serviceAccounts/\(serviceAccountEmail):generateAccessToken"
        )
        let response: ImpersonationResponse = try await http.postJSON(
            url: endpoint,
            body: ImpersonationRequest(scope: configuration.scopes, lifetime: "3600s"),
            headers: ["Authorization": "Bearer \(federatedToken)"]
        )
        guard let expiresAt = GCPAuthTimestamp.date(from: response.expireTime) else {
            throw GCPAuthError.malformedResponse(
                "Impersonation expireTime '\(response.expireTime)' was not RFC 3339."
            )
        }
        return GCPAuthToken(value: response.accessToken, expiresAt: expiresAt)
    }

    /// STS answers with OAuth-style snake_case, unlike most Google JSON APIs.
    /// `expires_in` is an int64, which protobuf-JSON is entitled to render as a
    /// string, so accept either rather than failing the whole exchange over it.
    private struct STSResponse: Decodable {
        let accessToken: String
        let tokenType: String?
        let expiresIn: TimeInterval

        enum CodingKeys: String, CodingKey {
            case accessToken = "access_token"
            case tokenType = "token_type"
            case expiresIn = "expires_in"
        }

        init(from decoder: Decoder) throws {
            let container = try decoder.container(keyedBy: CodingKeys.self)
            accessToken = try container.decode(String.self, forKey: .accessToken)
            tokenType = try container.decodeIfPresent(String.self, forKey: .tokenType)
            if let number = try? container.decode(Double.self, forKey: .expiresIn) {
                expiresIn = number
            } else {
                let text = try container.decode(String.self, forKey: .expiresIn)
                guard let parsed = TimeInterval(text) else {
                    throw DecodingError.dataCorruptedError(
                        forKey: .expiresIn,
                        in: container,
                        debugDescription: "expires_in '\(text)' was not a number"
                    )
                }
                expiresIn = parsed
            }
        }
    }

    private struct ImpersonationRequest: Encodable {
        let scope: [String]
        let lifetime: String
    }

    private struct ImpersonationResponse: Decodable {
        let accessToken: String
        let expireTime: String
    }
}

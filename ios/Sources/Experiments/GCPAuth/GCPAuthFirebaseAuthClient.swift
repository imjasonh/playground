import Foundation

/// Firebase Auth over its REST API (no Firebase SDK).
///
/// Every call carries the App Check token in `X-Firebase-AppCheck`. That header
/// is what lets you turn on App Check *enforcement* for Identity Platform, so
/// sign-in attempts that don't come from an attested install of this app are
/// refused before they ever mint an ID token.
struct GCPAuthFirebaseAuthClient {
    let configuration: GCPAuthConfiguration
    let http: GCPAuthHTTPClient

    private static let identityHost = "identitytoolkit.googleapis.com"
    private static let secureTokenHost = "securetoken.googleapis.com"

    /// Anonymous sign-in. It still produces a real, per-install Firebase user
    /// with a stable `sub`, which is enough for the federation step to work —
    /// and unlike Sign in with Apple it needs no entitlement, so the experiment
    /// runs without a signing bootstrap.
    func signInAnonymously(appCheckToken: String?) async throws -> GCPAuthIdentity {
        let endpoint = try GCPAuthURLBuilder.googleAPI(
            host: Self.identityHost,
            path: "v1/accounts:signUp",
            apiKey: configuration.apiKey
        )
        let response: SignInResponse = try await http.postJSON(
            url: endpoint,
            body: AnonymousSignInRequest(returnSecureToken: true),
            headers: Self.headers(appCheckToken: appCheckToken)
        )
        return try identity(from: response, provider: .anonymous)
    }

    /// Exchanges Apple's identity token for a Firebase one.
    ///
    /// `rawNonce` is the *unhashed* nonce. Apple's token carries `SHA256(nonce)`;
    /// Firebase hashes what you send here and compares, which is what proves this
    /// app requested that specific token instead of replaying someone else's.
    func signInWithApple(
        identityToken: String,
        rawNonce: String,
        appCheckToken: String?
    ) async throws -> GCPAuthIdentity {
        let postBody = [
            "id_token=\(GCPAuthForm.percentEncode(identityToken))",
            "providerId=apple.com",
            "nonce=\(GCPAuthForm.percentEncode(rawNonce))"
        ].joined(separator: "&")

        let endpoint = try GCPAuthURLBuilder.googleAPI(
            host: Self.identityHost,
            path: "v1/accounts:signInWithIdp",
            apiKey: configuration.apiKey
        )
        let response: SignInResponse = try await http.postJSON(
            url: endpoint,
            body: IdpSignInRequest(
                postBody: postBody,
                requestUri: configuration.authorizedDomainURL,
                returnIdpCredential: true,
                returnSecureToken: true
            ),
            headers: Self.headers(appCheckToken: appCheckToken)
        )
        return try identity(from: response, provider: .apple)
    }

    /// Firebase ID tokens last an hour. The refresh token is the long-lived
    /// secret on the device, which is why it belongs in the Keychain rather than
    /// anywhere it could be read at rest.
    func refresh(
        refreshToken: String,
        provider: GCPAuthIdentity.Provider,
        appCheckToken: String?
    ) async throws -> GCPAuthIdentity {
        let endpoint = try GCPAuthURLBuilder.googleAPI(
            host: Self.secureTokenHost,
            path: "v1/token",
            apiKey: configuration.apiKey
        )
        let response: RefreshResponse = try await http.postForm(
            url: endpoint,
            fields: [
                ("grant_type", "refresh_token"),
                ("refresh_token", refreshToken)
            ],
            headers: Self.headers(appCheckToken: appCheckToken)
        )
        guard let seconds = TimeInterval(response.expiresIn) else {
            throw GCPAuthError.malformedResponse("Refresh expires_in '\(response.expiresIn)' was not a number.")
        }
        return GCPAuthIdentity(
            idToken: GCPAuthToken(value: response.idToken, expiresAt: Date().addingTimeInterval(seconds)),
            refreshToken: response.refreshToken,
            userID: response.userId,
            provider: provider
        )
    }

    private static func headers(appCheckToken: String?) -> [String: String] {
        guard let appCheckToken, !appCheckToken.isEmpty else { return [:] }
        return ["X-Firebase-AppCheck": appCheckToken]
    }

    private func identity(
        from response: SignInResponse,
        provider: GCPAuthIdentity.Provider,
        now: Date = Date()
    ) throws -> GCPAuthIdentity {
        guard let seconds = TimeInterval(response.expiresIn) else {
            throw GCPAuthError.malformedResponse("Sign-in expiresIn '\(response.expiresIn)' was not a number.")
        }
        return GCPAuthIdentity(
            idToken: GCPAuthToken(value: response.idToken, expiresAt: now.addingTimeInterval(seconds)),
            refreshToken: response.refreshToken,
            userID: response.localId,
            provider: provider
        )
    }

    private struct AnonymousSignInRequest: Encodable {
        let returnSecureToken: Bool
    }

    private struct IdpSignInRequest: Encodable {
        let postBody: String
        let requestUri: String
        let returnIdpCredential: Bool
        let returnSecureToken: Bool
    }

    /// Identity Toolkit sends `expiresIn` as a string, not a number.
    private struct SignInResponse: Decodable {
        let idToken: String
        let refreshToken: String
        let expiresIn: String
        let localId: String
    }

    private struct RefreshResponse: Decodable {
        let idToken: String
        let refreshToken: String
        let expiresIn: String
        let userId: String

        enum CodingKeys: String, CodingKey {
            case idToken = "id_token"
            case refreshToken = "refresh_token"
            case expiresIn = "expires_in"
            case userId = "user_id"
        }
    }
}

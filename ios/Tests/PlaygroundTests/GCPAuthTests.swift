import CryptoKit
import XCTest
@testable import Playground

// MARK: - Test doubles

/// Wraps the shipped simulated transport so tests can see the exact requests the
/// chain built, and can make individual endpoints fail on demand.
private final class RecordingTransport: GCPAuthTransport {
    private let inner: GCPAuthSimulatedTransport
    private(set) var requests: [URLRequest] = []
    /// Path suffix → number of times to answer with the given failure first.
    var failures: [String: (remaining: Int, status: Int, message: String)] = [:]

    init(configuration: GCPAuthConfiguration) {
        self.inner = GCPAuthSimulatedTransport(configuration: configuration)
    }

    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse) {
        requests.append(request)
        guard let url = request.url else {
            throw GCPAuthError.badURL("<no url>")
        }
        for (suffix, failure) in failures where url.path.hasSuffix(suffix) && failure.remaining > 0 {
            failures[suffix] = (failure.remaining - 1, failure.status, failure.message)
            let body: [String: Any] = [
                "error": ["code": failure.status, "message": failure.message, "status": "PERMISSION_DENIED"]
            ]
            let data = try JSONSerialization.data(withJSONObject: body)
            let response = HTTPURLResponse(
                url: url,
                statusCode: failure.status,
                httpVersion: "HTTP/1.1",
                headerFields: nil
            )!
            return (data, response)
        }
        return try await inner.send(request)
    }

    func paths() -> [String] {
        requests.compactMap { $0.url?.path }
    }

    func body(forPathSuffix suffix: String) -> String? {
        guard let request = requests.last(where: { $0.url?.path.hasSuffix(suffix) == true }),
              let data = request.httpBody else {
            return nil
        }
        return String(decoding: data, as: UTF8.self)
    }

    func header(_ name: String, forPathSuffix suffix: String) -> String? {
        requests
            .last { $0.url?.path.hasSuffix(suffix) == true }?
            .value(forHTTPHeaderField: name)
    }
}

private func makeConfiguration(serviceAccountEmail: String = "") -> GCPAuthConfiguration {
    var configuration = GCPAuthConfiguration.unconfigured
    configuration.projectID = "playground-demo"
    configuration.projectNumber = "123456789012"
    configuration.apiKey = "AIzaSyExampleKey"
    configuration.appID = "1:123456789012:ios:abc123def456"
    configuration.serviceAccountEmail = serviceAccountEmail
    return configuration
}

// MARK: - Small pieces

final class GCPAuthPrimitivesTests: XCTestCase {
    func testDurationParsesGoogleStyleSeconds() {
        XCTAssertEqual(GCPAuthDuration.seconds(from: "3600s"), 3600)
        XCTAssertEqual(GCPAuthDuration.seconds(from: "60"), 60)
        XCTAssertEqual(GCPAuthDuration.seconds(from: "1.5s"), 1.5)
        XCTAssertNil(GCPAuthDuration.seconds(from: "soon"))
    }

    func testTimestampParsesWithAndWithoutFractionalSeconds() {
        XCTAssertNotNil(GCPAuthTimestamp.date(from: "2026-08-09T23:00:00Z"))
        XCTAssertNotNil(GCPAuthTimestamp.date(from: "2026-08-09T23:00:00.250Z"))
        XCTAssertNil(GCPAuthTimestamp.date(from: "tomorrow"))
    }

    func testBase64DecodeAcceptsURLSafeAndUnpadded() {
        let original = Data([0xFB, 0xFF, 0xBE, 0x01, 0x02])
        let standard = original.base64EncodedString()
        let urlSafe = GCPAuthBase64.encodeURLSafe(original)

        XCTAssertNotEqual(standard, urlSafe, "This payload should differ between the two alphabets")
        XCTAssertEqual(GCPAuthBase64.decode(standard), original)
        XCTAssertEqual(GCPAuthBase64.decode(urlSafe), original)
    }

    func testFormBodyPercentEncodesReservedCharacters() {
        let body = GCPAuthForm.body([
            ("grant_type", "urn:ietf:params:oauth:grant-type:token-exchange"),
            ("scope", "https://www.googleapis.com/auth/cloud-platform")
        ])
        let text = String(decoding: body, as: UTF8.self)
        XCTAssertEqual(
            text,
            "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Atoken-exchange"
                + "&scope=https%3A%2F%2Fwww.googleapis.com%2Fauth%2Fcloud-platform"
        )
    }

    func testTokenIsTreatedAsExpiredBeforeItActuallyIs() {
        let now = Date()
        let token = GCPAuthToken(value: "t", expiresAt: now.addingTimeInterval(30))
        XCTAssertFalse(token.isValid(at: now), "30s of life is inside the refresh skew")
        XCTAssertTrue(GCPAuthToken(value: "t", expiresAt: now.addingTimeInterval(600)).isValid(at: now))
    }

    func testRedactedTokenDoesNotLeakTheWholeValue() {
        let token = GCPAuthToken(value: String(repeating: "x", count: 400), expiresAt: Date())
        XCTAssertFalse(token.redacted.contains(String(repeating: "x", count: 20)))
        XCTAssertTrue(token.redacted.contains("400 chars"))
    }

    func testGoogleErrorEnvelopeBecomesTheMessage() {
        let data = Data(#"{"error":{"code":403,"message":"App attestation failed","status":"PERMISSION_DENIED"}}"#.utf8)
        XCTAssertEqual(GCPAuthHTTPClient.errorMessage(from: data), "App attestation failed")
    }

    func testNonEnvelopeErrorFallsBackToTheRawBody() {
        XCTAssertEqual(GCPAuthHTTPClient.errorMessage(from: Data("nope".utf8)), "nope")
    }
}

final class GCPAuthConfigurationTests: XCTestCase {
    func testShippedConfigurationIsNotConsideredConfigured() {
        XCTAssertFalse(GCPAuthConfiguration.unconfigured.isConfigured)
    }

    func testFilledConfigurationIsConfigured() {
        XCTAssertTrue(makeConfiguration().isConfigured)
    }

    func testPlaceholderAppIDIsRejectedEvenWhenEverythingElseIsReal() {
        var configuration = makeConfiguration()
        configuration.appID = "1:000000000000:ios:0000000000000000"
        XCTAssertFalse(configuration.isConfigured)
    }

    func testDerivedGoogleIdentifiers() {
        let configuration = makeConfiguration()
        XCTAssertEqual(configuration.firebaseIssuer, "https://securetoken.google.com/playground-demo")
        XCTAssertEqual(
            configuration.workloadIdentityAudience,
            "//iam.googleapis.com/projects/123456789012/locations/global"
                + "/workloadIdentityPools/playground-ios-pool/providers/firebase-auth"
        )
        XCTAssertEqual(configuration.appCheckResource, "projects/123456789012/apps/1:123456789012:ios:abc123def456")
    }

    func testBundleWithoutAGCPAuthKeyFallsBackToUnconfigured() {
        XCTAssertEqual(GCPAuthConfiguration.fromBundle(.main), .unconfigured)
    }
}

final class GCPAuthJWTTests: XCTestCase {
    func testDecodesStandardClaims() {
        let token = GCPAuthSimulatedTransport.unsignedJWT([
            "iss": "https://securetoken.google.com/playground-demo",
            "aud": "playground-demo",
            "sub": "user-1",
            "iat": 1_700_000_000,
            "exp": 1_700_003_600,
            "firebase": ["sign_in_provider": "anonymous"]
        ])

        let claims = GCPAuthJWT.decode(token)
        XCTAssertEqual(claims?.issuer, "https://securetoken.google.com/playground-demo")
        XCTAssertEqual(claims?.audience, "playground-demo")
        XCTAssertEqual(claims?.subject, "user-1")
        XCTAssertEqual(claims?.expiresAt, Date(timeIntervalSince1970: 1_700_003_600))
        XCTAssertEqual(claims?.all.map(\.name), ["aud", "exp", "firebase", "iat", "iss", "sub"])
        XCTAssertEqual(
            claims?.all.first { $0.name == "firebase" }?.value,
            "sign_in_provider=anonymous"
        )
    }

    func testDecodesArrayAudience() {
        let token = GCPAuthSimulatedTransport.unsignedJWT(["aud": ["projects/1", "projects/two"]])
        XCTAssertEqual(GCPAuthJWT.decode(token)?.audience, "projects/1, projects/two")
    }

    func testRejectsThingsThatAreNotJWTs() {
        XCTAssertNil(GCPAuthJWT.decode("ya29.an-opaque-google-access-token"))
        XCTAssertNil(GCPAuthJWT.decode("a.b"))
        XCTAssertNil(GCPAuthJWT.decode("aGVhZGVy.bm90LWpzb24.c2ln"))
    }
}

final class GCPAuthClientDataTests: XCTestCase {
    func testAttestationHashesOnlyTheChallenge() {
        let challenge = Data("challenge".utf8)
        XCTAssertEqual(
            GCPAuthClientData.attestationHash(challenge: challenge),
            Data(SHA256.hash(data: challenge))
        )
    }

    func testAssertionBindsArtifactAndChallengeTogether() {
        let artifact = Data("artifact".utf8)
        let challenge = Data("challenge".utf8)
        XCTAssertEqual(
            GCPAuthClientData.assertionHash(artifact: artifact, challenge: challenge),
            Data(SHA256.hash(data: artifact + challenge))
        )
        XCTAssertNotEqual(
            GCPAuthClientData.assertionHash(artifact: artifact, challenge: challenge),
            GCPAuthClientData.attestationHash(challenge: challenge)
        )
    }

    func testEachChallengeProducesADifferentAssertionHash() {
        let artifact = Data("artifact".utf8)
        XCTAssertNotEqual(
            GCPAuthClientData.assertionHash(artifact: artifact, challenge: Data("one".utf8)),
            GCPAuthClientData.assertionHash(artifact: artifact, challenge: Data("two".utf8))
        )
    }
}

// MARK: - The chain

final class GCPAuthCredentialChainTests: XCTestCase {
    private func makeChain(
        configuration: GCPAuthConfiguration,
        store: GCPAuthStateStore = GCPAuthInMemoryStore(),
        attestor: GCPAuthAttestor = GCPAuthSimulatedAttestor(),
        transport: RecordingTransport
    ) -> GCPAuthCredentialChain {
        .make(configuration: configuration, store: store, attestor: attestor, transport: transport)
    }

    func testFirstRunAttestsAKeyAndStoresTheArtifact() async throws {
        let configuration = makeConfiguration()
        let store = GCPAuthInMemoryStore()
        let attestor = GCPAuthSimulatedAttestor()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, store: store, attestor: attestor, transport: transport)

        let token = try await chain.appCheckToken()

        XCTAssertFalse(token.value.isEmpty)
        XCTAssertEqual(store.appAttestKeyID, "simulated-key-1")
        XCTAssertNotNil(store.appCheckArtifact)
        XCTAssertEqual(attestor.attestedHashes.count, 1)
        XCTAssertTrue(attestor.assertedHashes.isEmpty)
        XCTAssertTrue(transport.paths().contains { $0.hasSuffix(":exchangeAppAttestAttestation") })
    }

    func testSecondRunAssertsTheStoredKeyInsteadOfAttestingAgain() async throws {
        let configuration = makeConfiguration()
        let store = GCPAuthInMemoryStore()
        let attestor = GCPAuthSimulatedAttestor()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, store: store, attestor: attestor, transport: transport)

        _ = try await chain.appCheckToken()
        _ = try await chain.appCheckToken()

        XCTAssertEqual(attestor.generatedKeyCount, 1, "The Secure Enclave key is generated once")
        XCTAssertEqual(attestor.attestedHashes.count, 1)
        XCTAssertEqual(attestor.assertedHashes.count, 1)
    }

    func testARejectedAssertionReattestsOnceRatherThanStrandingTheInstall() async throws {
        let configuration = makeConfiguration()
        let store = GCPAuthInMemoryStore()
        let attestor = GCPAuthSimulatedAttestor()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, store: store, attestor: attestor, transport: transport)

        _ = try await chain.appCheckToken()
        transport.failures[":exchangeAppAttestAssertion"] = (remaining: 1, status: 403, message: "artifact expired")

        let recovered = try await chain.appCheckToken()

        XCTAssertFalse(recovered.value.isEmpty)
        XCTAssertEqual(attestor.generatedKeyCount, 2, "A fresh key is attested after the rejection")
        XCTAssertEqual(attestor.attestedHashes.count, 2)
        XCTAssertEqual(store.appAttestKeyID, "simulated-key-2")
    }

    func testAServerErrorOnAssertionIsNotTreatedAsAStaleKey() async throws {
        let configuration = makeConfiguration()
        let store = GCPAuthInMemoryStore()
        let attestor = GCPAuthSimulatedAttestor()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, store: store, attestor: attestor, transport: transport)

        _ = try await chain.appCheckToken()
        transport.failures[":exchangeAppAttestAssertion"] = (remaining: 1, status: 503, message: "backend down")

        do {
            _ = try await chain.appCheckToken()
            XCTFail("A 5xx should surface rather than burning a new App Attest key")
        } catch let error as GCPAuthError {
            guard case .http(let status, _) = error else {
                return XCTFail("Expected an HTTP error, got \(error)")
            }
            XCTAssertEqual(status, 503)
        }
        XCTAssertEqual(attestor.generatedKeyCount, 1)
    }

    func testSignInCarriesTheAppCheckTokenAsAHeader() async throws {
        let configuration = makeConfiguration()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, transport: transport)

        let identity = try await chain.signIn(appCheckToken: "app-check-token-value")

        XCTAssertEqual(identity.provider, .anonymous)
        XCTAssertEqual(identity.userID, "simulated-user-0001")
        XCTAssertEqual(
            transport.header("X-Firebase-AppCheck", forPathSuffix: "accounts:signUp"),
            "app-check-token-value"
        )
    }

    func testFederationSendsAnRFC8693TokenExchange() async throws {
        let configuration = makeConfiguration()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, transport: transport)

        let token = try await chain.googleAccessToken(firebaseIDToken: "firebase.id.token")

        XCTAssertTrue(token.value.hasPrefix("ya29."))
        let body = try XCTUnwrap(transport.body(forPathSuffix: "v1/token"))
        XCTAssertTrue(body.contains("grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Atoken-exchange"))
        XCTAssertTrue(body.contains("subject_token=firebase.id.token"))
        XCTAssertTrue(body.contains("subject_token_type=urn%3Aietf%3Aparams%3Aoauth%3Atoken-type%3Ajwt"))
        XCTAssertTrue(body.contains("workloadIdentityPools"))
    }

    func testFederationStopsAtTheFederatedPrincipalWhenNoServiceAccountIsSet() async throws {
        let configuration = makeConfiguration()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, transport: transport)

        _ = try await chain.googleAccessToken(firebaseIDToken: "firebase.id.token")

        XCTAssertFalse(transport.paths().contains { $0.hasSuffix(":generateAccessToken") })
    }

    func testFederationImpersonatesWhenAServiceAccountIsConfigured() async throws {
        let configuration = makeConfiguration(serviceAccountEmail: "ios-app@playground-demo.iam.gserviceaccount.com")
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, transport: transport)

        let token = try await chain.googleAccessToken(firebaseIDToken: "firebase.id.token")

        XCTAssertTrue(token.value.contains("impersonated"))
        XCTAssertEqual(
            transport.header("Authorization", forPathSuffix: ":generateAccessToken")?.hasPrefix("Bearer ya29."),
            true
        )
    }

    func testWholeChainProducesAGoogleAccessTokenAndAnInspectableIDToken() async throws {
        let configuration = makeConfiguration()
        let transport = RecordingTransport(configuration: configuration)
        let chain = makeChain(configuration: configuration, transport: transport)

        let appCheck = try await chain.appCheckToken()
        let identity = try await chain.signIn(appCheckToken: appCheck.value)
        let access = try await chain.googleAccessToken(firebaseIDToken: identity.idToken.value)

        let claims = try XCTUnwrap(GCPAuthJWT.decode(identity.idToken.value))
        XCTAssertEqual(claims.issuer, configuration.firebaseIssuer)
        XCTAssertEqual(claims.audience, configuration.projectID)
        XCTAssertTrue(access.isValid(at: Date()))
        XCTAssertNil(GCPAuthJWT.decode(access.value), "Google access tokens are opaque, not JWTs")
    }
}

// MARK: - The flow the UI drives

final class GCPAuthFlowModelTests: XCTestCase {
    @MainActor
    private func makeModel(configuration: GCPAuthConfiguration) -> GCPAuthFlowModel {
        let store = GCPAuthInMemoryStore()
        return GCPAuthFlowModel(
            configuration: configuration,
            store: store,
            chain: .make(
                configuration: configuration,
                store: store,
                attestor: GCPAuthSimulatedAttestor(),
                transport: RecordingTransport(configuration: configuration)
            )
        )
    }

    @MainActor
    func testEveryStepStartsPending() {
        let model = makeModel(configuration: makeConfiguration())
        for step in GCPAuthStep.allCases {
            XCTAssertEqual(model.state(for: step), .pending)
        }
        XCTAssertFalse(model.isRunning)
    }

    @MainActor
    func testRunWalksEveryStepToSuccess() async {
        let model = makeModel(configuration: makeConfiguration())

        await model.run()

        for step in GCPAuthStep.allCases {
            guard case .succeeded = model.state(for: step) else {
                return XCTFail("\(step.rawValue) did not succeed: \(model.state(for: step))")
            }
            XCTAssertNotNil(model.tokens[step])
        }
        XCTAssertEqual(model.identity?.provider, .anonymous)
        XCTAssertFalse(model.isRunning)
        XCTAssertNotNil(model.claims(for: .signIn))
    }

    @MainActor
    func testResetClearsTokensAndStepStates() async {
        let model = makeModel(configuration: makeConfiguration())
        await model.run()

        model.reset()

        XCTAssertTrue(model.tokens.isEmpty)
        XCTAssertNil(model.identity)
        for step in GCPAuthStep.allCases {
            XCTAssertEqual(model.state(for: step), .pending)
        }
    }

    @MainActor
    func testUnconfiguredBuildAnnouncesItselfAsSimulated() {
        let model = GCPAuthFlowModel()
        XCTAssertTrue(model.isSimulated, "The checked-in app ships without a project")
        XCTAssertTrue(model.statusMessage.localizedCaseInsensitiveContains("simulated"))
    }

    @MainActor
    func testSimulatedBuildStillCompletesTheWholeChain() async {
        let model = GCPAuthFlowModel()

        await model.run()

        for step in GCPAuthStep.allCases {
            guard case .succeeded = model.state(for: step) else {
                return XCTFail("\(step.rawValue) did not succeed in simulated mode")
            }
        }
    }
}

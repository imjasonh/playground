import AuthenticationServices
import CryptoKit
import XCTest
@testable import Playground

final class AppAttestTests: XCTestCase {
    func testClientDataJSONIsSortedAndCompact() throws {
        let data = AppAttestClientData(
            challenge: "chal-1",
            userId: "user-1",
            deviceId: "device-1"
        )
        let json = try data.jsonBytes()
        XCTAssertEqual(
            String(data: json, encoding: .utf8),
            #"{"challenge":"chal-1","deviceId":"device-1","userId":"user-1"}"#
        )
    }

    func testAssertionClientDataJSONIsSortedAndCompact() throws {
        let data = AppAttestAssertionClientData(action: "whoami", challenge: "c1")
        let json = try data.jsonBytes()
        XCTAssertEqual(
            String(data: json, encoding: .utf8),
            #"{"action":"whoami","challenge":"c1"}"#
        )
    }

    func testClientDataHashMatchesSHA256OfExactBytes() throws {
        let data = AppAttestClientData(
            challenge: "abc",
            userId: "u",
            deviceId: "d"
        )
        let json = try data.jsonBytes()
        XCTAssertEqual(
            AppAttestHashing.sha256(json),
            Data(SHA256.hash(data: json))
        )
    }

    func testAPIDecodesChallengeAndWhoami() async throws {
        let http = FakeAppAttestHTTP()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(
                    #"{"challenge":"nonce-1","expiresAt":1700000000}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/whoami") {
                XCTAssertEqual(request.httpMethod, "POST")
                let body = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(body?["keyId"] as? String, "k")
                XCTAssertEqual(body?["assertionObject"] as? String, Data([0xAA]).base64EncodedString())
                XCTAssertEqual(body?["clientData"] as? String, #"{"action":"whoami","challenge":"n"}"#)
                return Self.json(
                    #"{"userId":"u","deviceId":"d","keyId":"k","unattested":false,"counter":1}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"not found"}"#, status: 404)
        }
        let api = AppAttestAPI(
            baseURL: URL(string: "https://example.test")!,
            http: http
        )
        let challenge = try await api.fetchChallenge()
        XCTAssertEqual(challenge.challenge, "nonce-1")
        let who = try await api.whoami(
            keyId: "k",
            assertionObject: Data([0xAA]),
            clientDataJSON: Data(#"{"action":"whoami","challenge":"n"}"#.utf8)
        )
        XCTAssertEqual(who.userId, "u")
        XCTAssertEqual(who.deviceId, "d")
        XCTAssertEqual(who.counter, 1)
        XCTAssertFalse(who.unattested)
    }

    func testAPISurfacesServerError() async {
        let http = FakeAppAttestHTTP()
        http.onRequest = { _ in
            Self.json(#"{"error":"challenge expired"}"#, status: 400)
        }
        let api = AppAttestAPI(
            baseURL: URL(string: "https://example.test")!,
            http: http
        )
        do {
            _ = try await api.fetchChallenge()
            XCTFail("expected error")
        } catch let error as AppAttestAPIError {
            XCTAssertEqual(error, .server(status: 400, message: "challenge expired"))
        } catch {
            XCTFail("unexpected \(error)")
        }
    }

    @MainActor
    func testRegisterUnattestedThenWhoami() async throws {
        let store = AppAttestMemoryStore(deviceId: "dev-9", userId: "")
        let keys = FakeAppAttestKeys(isSupported: false)
        let http = FakeAppAttestHTTP()
        let challenges = IntBox()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challenges.increment()
                return Self.json(
                    #"{"challenge":"n\(n)","expiresAt":1}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/unattested-token") {
                let object = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(
                    object?["clientData"] as? String,
                    #"{"challenge":"n1","deviceId":"dev-9","userId":"alice"}"#
                )
                return Self.json(
                    #"{"userId":"alice","deviceId":"dev-9","keyId":"unattested:dev-9","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/whoami") {
                XCTAssertEqual(request.httpMethod, "POST")
                let object = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(object?["keyId"] as? String, "unattested:dev-9")
                XCTAssertEqual(
                    object?["clientData"] as? String,
                    #"{"action":"whoami","challenge":"n2"}"#
                )
                XCTAssertNil(object?["assertionObject"])
                return Self.json(
                    #"{"userId":"alice","deviceId":"dev-9","keyId":"unattested:dev-9","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected \(path)"}"#, status: 500)
        }

        let controller = AppAttestController(
            keys: keys,
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.applyAppleSignIn(.success("alice"))
        XCTAssertTrue(controller.isRegistered)
        XCTAssertFalse(controller.statusIsError)
        XCTAssertEqual(controller.lastWhoAmI?.userId, "alice")
        XCTAssertEqual(controller.lastWhoAmI?.deviceId, "dev-9")
        XCTAssertEqual(controller.lastWhoAmI?.unattested, true)
        XCTAssertEqual(store.keyId, "unattested:dev-9")
        XCTAssertTrue(store.isRegistered)
        XCTAssertEqual(controller.statusMessage, "Worker accepted the unattested whoami.")
    }

    @MainActor
    func testRegisterAttestedSendsKeyAndHashBytes() async throws {
        let store = AppAttestMemoryStore(deviceId: "dev-a", userId: "bob")
        let keys = FakeAppAttestKeys(
            isSupported: true,
            keyId: "key-xyz",
            attestation: Data([0xDE, 0xAD])
        )
        let http = FakeAppAttestHTTP()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(#"{"challenge":"c1","expiresAt":1}"#, status: 200)
            }
            if path.hasSuffix("/v1/token") {
                let body = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(body?["keyId"] as? String, "key-xyz")
                XCTAssertEqual(body?["attestationObject"] as? String, Data([0xDE, 0xAD]).base64EncodedString())
                let client = body?["clientData"] as? String
                XCTAssertEqual(client, #"{"challenge":"c1","deviceId":"dev-a","userId":"bob"}"#)
                return Self.json(
                    #"{"userId":"bob","deviceId":"dev-a","keyId":"key-xyz","unattested":false,"counter":0}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected"}"#, status: 500)
        }

        let controller = AppAttestController(
            keys: keys,
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.register()
        XCTAssertEqual(store.keyId, "key-xyz")
        XCTAssertEqual(keys.lastClientDataHash, AppAttestHashing.sha256(
            Data(#"{"challenge":"c1","deviceId":"dev-a","userId":"bob"}"#.utf8)
        ))
        XCTAssertEqual(controller.lastWhoAmI?.unattested, false)
        XCTAssertEqual(controller.statusMessage, "Device attested.")
    }

    @MainActor
    func testWhoamiAttestedSendsAssertion() async throws {
        let store = AppAttestMemoryStore(deviceId: "dev-a", userId: "bob")
        store.keyId = "key-xyz"
        store.isRegistered = true
        let keys = FakeAppAttestKeys(
            isSupported: true,
            keyId: "key-xyz",
            assertion: Data([0xBE, 0xEF])
        )
        let http = FakeAppAttestHTTP()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(#"{"challenge":"c2","expiresAt":1}"#, status: 200)
            }
            if path.hasSuffix("/v1/whoami") {
                let body = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(body?["keyId"] as? String, "key-xyz")
                XCTAssertEqual(body?["assertionObject"] as? String, Data([0xBE, 0xEF]).base64EncodedString())
                XCTAssertEqual(body?["clientData"] as? String, #"{"action":"whoami","challenge":"c2"}"#)
                return Self.json(
                    #"{"userId":"bob","deviceId":"dev-a","keyId":"key-xyz","unattested":false,"counter":4,"riskMetric":1}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected \(path)"}"#, status: 500)
        }
        let controller = AppAttestController(
            keys: keys,
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.whoami()
        XCTAssertEqual(keys.lastAssertionHash, AppAttestHashing.sha256(
            Data(#"{"action":"whoami","challenge":"c2"}"#.utf8)
        ))
        XCTAssertEqual(controller.lastWhoAmI?.counter, 4)
        XCTAssertEqual(controller.lastWhoAmI?.riskMetric, 1)
        XCTAssertEqual(controller.statusMessage, "Worker accepted the assertion.")
    }

    @MainActor
    func testEmptyUserIdDoesNotCallNetwork() async {
        let store = AppAttestMemoryStore(userId: "")
        let http = FakeAppAttestHTTP()
        http.onRequest = { _ in
            XCTFail("network should not run")
            return Self.json("{}", status: 500)
        }
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.register()
        XCTAssertFalse(controller.isRegistered)
        XCTAssertFalse(controller.isSignedIn)
        XCTAssertTrue(controller.statusIsError)
        XCTAssertEqual(controller.statusMessage, "Sign in with Apple first.")
    }

    @MainActor
    func testRegisterSurfacesWorkerError() async {
        let store = AppAttestMemoryStore(userId: "alice")
        let http = FakeAppAttestHTTP()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(
                    #"{"challenge":"n","expiresAt":1}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"certificate: issuer P-256 key"}"#, status: 400)
        }
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.register()
        XCTAssertFalse(controller.isRegistered)
        XCTAssertTrue(controller.statusIsError)
        XCTAssertEqual(
            controller.statusMessage,
            "Register failed: certificate: issuer P-256 key"
        )
    }

    @MainActor
    func testSignInRegistersDevice() async {
        let store = AppAttestMemoryStore(userId: "")
        let http = FakeAppAttestHTTP()
        let challenges = IntBox()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challenges.increment()
                return Self.json(#"{"challenge":"n\(n)","expiresAt":1}"#, status: 200)
            }
            if path.hasSuffix("/v1/unattested-token") {
                return Self.json(
                    #"{"userId":"001234.apple-user","deviceId":"device-test","keyId":"unattested:device-test","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/whoami") {
                return Self.json(
                    #"{"userId":"001234.apple-user","deviceId":"device-test","keyId":"unattested:device-test","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected \(path)"}"#, status: 500)
        }
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        XCTAssertFalse(controller.isSignedIn)
        await controller.applyAppleSignIn(.success("001234.apple-user"))
        XCTAssertTrue(controller.isSignedIn)
        XCTAssertTrue(controller.isRegistered)
        XCTAssertEqual(controller.userId, "001234.apple-user")
        XCTAssertEqual(store.userId, "001234.apple-user")
        XCTAssertEqual(store.keyId, "unattested:device-test")
        XCTAssertEqual(controller.lastWhoAmI?.userId, "001234.apple-user")
        XCTAssertEqual(controller.lastWhoAmI?.deviceId, "device-test")
        XCTAssertEqual(controller.lastWhoAmI?.unattested, true)
        XCTAssertFalse(controller.statusIsError)
        XCTAssertEqual(controller.statusMessage, "Worker accepted the unattested whoami.")
    }

    @MainActor
    func testApplyAppleUserIDDoesNotRegisterByItself() {
        let store = AppAttestMemoryStore(userId: "")
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        XCTAssertFalse(controller.isSignedIn)
        controller.applyAppleUserID("001234.apple-user")
        XCTAssertTrue(controller.isSignedIn)
        XCTAssertFalse(controller.isRegistered)
        XCTAssertEqual(controller.userId, "001234.apple-user")
        XCTAssertEqual(store.userId, "001234.apple-user")
        XCTAssertEqual(controller.statusMessage, "Signed in with Apple.")
    }

    func testAppleSignInMapsCanceledAuthorizationError() {
        let mapped = AppAttestAppleSignIn.userID(from: .failure(ASAuthorizationError(.canceled)))
        guard case .failure(.canceled) = mapped else {
            return XCTFail("expected canceled, got \(mapped)")
        }
    }

    @MainActor
    func testCanceledSignInLeavesUserUnsigned() async {
        let store = AppAttestMemoryStore(userId: "")
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.applyAppleSignIn(.failure(.canceled))
        XCTAssertFalse(controller.isSignedIn)
        XCTAssertEqual(controller.statusMessage, "Sign in canceled.")
    }

    @MainActor
    func testSignOutClearsUserRegistrationAndKey() {
        let store = AppAttestMemoryStore(userId: "apple-1")
        store.isRegistered = true
        store.keyId = "key-1"
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        controller.signOut()
        XCTAssertFalse(controller.isSignedIn)
        XCTAssertFalse(controller.isRegistered)
        XCTAssertEqual(store.userId, "")
        XCTAssertFalse(store.isRegistered)
        XCTAssertNil(store.keyId)
        XCTAssertNil(controller.lastWhoAmI)
        XCTAssertEqual(controller.statusMessage, "Signed out.")
    }

    @MainActor
    func testSwitchingAppleUserClearsOldRegistration() {
        let store = AppAttestMemoryStore(userId: "apple-1")
        store.isRegistered = true
        store.keyId = "old-key"
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        XCTAssertTrue(controller.isRegistered)
        controller.applyAppleUserID("apple-2")
        XCTAssertEqual(controller.userId, "apple-2")
        XCTAssertFalse(controller.isRegistered)
        XCTAssertFalse(store.isRegistered)
        XCTAssertNil(store.keyId)
    }

    @MainActor
    func testRefreshRegistersWhenSignedInWithoutRegistration() async {
        let store = AppAttestMemoryStore(userId: "apple-saved")
        let http = FakeAppAttestHTTP()
        let challenges = IntBox()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                let n = challenges.increment()
                return Self.json(#"{"challenge":"n\(n)","expiresAt":1}"#, status: 200)
            }
            if path.hasSuffix("/v1/unattested-token") {
                return Self.json(
                    #"{"userId":"apple-saved","deviceId":"device-test","keyId":"unattested:device-test","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/whoami") {
                return Self.json(
                    #"{"userId":"apple-saved","deviceId":"device-test","keyId":"unattested:device-test","unattested":true,"counter":0}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected \(path)"}"#, status: 500)
        }
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        XCTAssertFalse(controller.isRegistered)
        await controller.refreshAppleIDState()
        XCTAssertTrue(controller.isRegistered)
        XCTAssertEqual(store.keyId, "unattested:device-test")
        XCTAssertEqual(controller.lastWhoAmI?.userId, "apple-saved")
        XCTAssertFalse(controller.statusIsError)
        XCTAssertEqual(controller.statusMessage, "Worker accepted the unattested whoami.")
    }

    @MainActor
    func testRefreshWhenRegisteredCallsWhoami() async {
        let store = AppAttestMemoryStore(userId: "apple-saved")
        store.isRegistered = true
        store.keyId = "key-1"
        let http = FakeAppAttestHTTP()
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(#"{"challenge":"n","expiresAt":1}"#, status: 200)
            }
            XCTAssertTrue(path.hasSuffix("/v1/whoami"), "expected whoami, got \(path)")
            return Self.json(
                #"{"userId":"apple-saved","deviceId":"device-test","keyId":"key-1","unattested":false,"counter":2}"#,
                status: 200
            )
        }
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: true, keyId: "key-1"),
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store,
            appleID: FakeAppAttestAppleID()
        )
        await controller.refreshAppleIDState()
        XCTAssertEqual(controller.lastWhoAmI?.userId, "apple-saved")
        XCTAssertEqual(controller.lastWhoAmI?.deviceId, "device-test")
        XCTAssertEqual(controller.lastWhoAmI?.keyId, "key-1")
        XCTAssertEqual(controller.lastWhoAmI?.unattested, false)
        XCTAssertEqual(controller.statusMessage, "Worker accepted the assertion.")
    }

    @MainActor
    func testRevokedAppleIDClearsSession() async {
        let store = AppAttestMemoryStore(userId: "apple-revoked")
        store.isRegistered = true
        store.keyId = "key-keep"
        let appleID = FakeAppAttestAppleID(state: .revoked)
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store,
            appleID: appleID
        )
        await controller.refreshAppleIDState()
        XCTAssertFalse(controller.isSignedIn)
        XCTAssertFalse(controller.isRegistered)
        XCTAssertNil(store.keyId)
        XCTAssertTrue(controller.statusIsError)
        XCTAssertEqual(controller.statusMessage, "Sign in with Apple was revoked. Sign in again.")
    }

    private static func json(_ body: String, status: Int) -> (Data, URLResponse) {
        let response = HTTPURLResponse(
            url: URL(string: "https://example.test")!,
            statusCode: status,
            httpVersion: "HTTP/1.1",
            headerFields: ["Content-Type": "application/json"]
        )!
        return (Data(body.utf8), response)
    }
}

private final class FakeAppAttestHTTP: AppAttestHTTPClient, @unchecked Sendable {
    var onRequest: @Sendable (URLRequest) throws -> (Data, URLResponse) = { _ in
        throw URLError(.badServerResponse)
    }

    func data(for request: URLRequest) async throws -> (Data, URLResponse) {
        try onRequest(request)
    }
}

private struct FakeAppAttestAppleID: AppAttestAppleIDChecking {
    var state: AppAttestAppleIDState = .authorized

    func credentialState(forUserID _: String) async -> AppAttestAppleIDState {
        state
    }
}

private struct FakeAppAttestKeys: AppAttestKeyGenerating {
    var isSupported: Bool
    var keyId: String = "fake-key"
    var attestation: Data = Data([0x01])
    var assertion: Data = Data([0x02])
    let lastClientDataHashBox = HashBox()
    let lastAssertionHashBox = HashBox()

    var lastClientDataHash: Data? { lastClientDataHashBox.value }
    var lastAssertionHash: Data? { lastAssertionHashBox.value }

    func generateKey() async throws -> String { keyId }

    func attestKey(_ keyId: String, clientDataHash: Data) async throws -> Data {
        lastClientDataHashBox.value = clientDataHash
        XCTAssertEqual(keyId, self.keyId)
        return attestation
    }

    func generateAssertion(_ keyId: String, clientDataHash: Data) async throws -> Data {
        lastAssertionHashBox.value = clientDataHash
        XCTAssertEqual(keyId, self.keyId)
        return assertion
    }
}

/// Lets the fake keys record the digest without making the struct a class.
private final class HashBox: @unchecked Sendable {
    var value: Data?
}

/// Lets a `@Sendable` HTTP stub increment a challenge count under Swift 6.
private final class IntBox: @unchecked Sendable {
    private var value = 0

    func increment() -> Int {
        value += 1
        return value
    }
}

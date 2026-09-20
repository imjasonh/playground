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
                XCTAssertEqual(request.value(forHTTPHeaderField: "Authorization"), "Bearer tok")
                return Self.json(
                    #"{"userId":"u","deviceId":"d","keyId":"k","unattested":false}"#,
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
        let who = try await api.whoami(token: "tok")
        XCTAssertEqual(who.userId, "u")
        XCTAssertEqual(who.deviceId, "d")
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
        http.onRequest = { request in
            let path = request.url?.path ?? ""
            if path.hasSuffix("/v1/challenge") {
                return Self.json(
                    #"{"challenge":"n","expiresAt":1}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/unattested-token") {
                let object = try JSONSerialization.jsonObject(with: request.httpBody ?? Data()) as? [String: Any]
                XCTAssertEqual(
                    object?["clientData"] as? String,
                    #"{"challenge":"n","deviceId":"dev-9","userId":"alice"}"#
                )
                return Self.json(
                    #"{"token":"jwt-1","expiresAt":2,"userId":"alice","deviceId":"dev-9","keyId":"unattested","unattested":true}"#,
                    status: 200
                )
            }
            if path.hasSuffix("/v1/whoami") {
                XCTAssertEqual(request.value(forHTTPHeaderField: "Authorization"), "Bearer jwt-1")
                return Self.json(
                    #"{"userId":"alice","deviceId":"dev-9","keyId":"unattested","unattested":true}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected \(path)"}"#, status: 500)
        }

        let controller = AppAttestController(
            keys: keys,
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store
        )
        controller.userId = "alice"
        await controller.register()
        XCTAssertTrue(controller.hasToken)
        XCTAssertEqual(controller.lastWhoAmI?.userId, "alice")
        XCTAssertEqual(controller.lastWhoAmI?.deviceId, "dev-9")
        XCTAssertEqual(controller.lastWhoAmI?.unattested, true)
        XCTAssertEqual(store.token, "jwt-1")

        await controller.whoami()
        XCTAssertEqual(controller.lastWhoAmI?.userId, "alice")
        XCTAssertTrue(controller.statusMessage.contains("unattested"))
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
                    #"{"token":"jwt-a","expiresAt":2,"userId":"bob","deviceId":"dev-a","keyId":"key-xyz","unattested":false}"#,
                    status: 200
                )
            }
            return Self.json(#"{"error":"unexpected"}"#, status: 500)
        }

        let controller = AppAttestController(
            keys: keys,
            api: AppAttestAPI(baseURL: URL(string: "https://example.test")!, http: http),
            store: store
        )
        await controller.register()
        XCTAssertEqual(store.keyId, "key-xyz")
        XCTAssertEqual(keys.lastClientDataHash, AppAttestHashing.sha256(
            Data(#"{"challenge":"c1","deviceId":"dev-a","userId":"bob"}"#.utf8)
        ))
        XCTAssertEqual(controller.lastWhoAmI?.unattested, false)
        XCTAssertEqual(controller.statusMessage, "Device attested. Token stored.")
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
            store: store
        )
        controller.userId = "   "
        await controller.register()
        XCTAssertFalse(controller.hasToken)
        XCTAssertEqual(controller.statusMessage, "Enter a user id.")
    }

    @MainActor
    func testForgetClearsToken() async {
        let store = AppAttestMemoryStore()
        store.token = "keep"
        store.keyId = "k"
        let controller = AppAttestController(
            keys: FakeAppAttestKeys(isSupported: false),
            store: store
        )
        XCTAssertTrue(controller.hasToken)
        controller.forgetToken()
        XCTAssertFalse(controller.hasToken)
        XCTAssertNil(store.token)
        XCTAssertNil(store.keyId)
        XCTAssertNil(controller.lastWhoAmI)
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

private struct FakeAppAttestKeys: AppAttestKeyGenerating {
    var isSupported: Bool
    var keyId: String = "fake-key"
    var attestation: Data = Data([0x01])
    let lastClientDataHashBox = HashBox()

    var lastClientDataHash: Data? { lastClientDataHashBox.value }

    func generateKey() async throws -> String { keyId }

    func attestKey(_ keyId: String, clientDataHash: Data) async throws -> Data {
        lastClientDataHashBox.value = clientDataHash
        XCTAssertEqual(keyId, self.keyId)
        return attestation
    }
}

/// Lets the fake keys record the digest without making the struct a class.
private final class HashBox: @unchecked Sendable {
    var value: Data?
}

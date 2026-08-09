import XCTest
@testable import Playground

final class ContainerLabBearerChallengeTests: XCTestCase {
    func testParsesDockerHubChallenge() throws {
        let header = #"Bearer realm="https://auth.docker.io/token",service="registry.docker.io",scope="repository:library/alpine:pull""#
        let challenge = try XCTUnwrap(BearerChallenge.parse(header))

        XCTAssertEqual(challenge.realm, "https://auth.docker.io/token")
        XCTAssertEqual(challenge.service, "registry.docker.io")
        XCTAssertEqual(challenge.scope, "repository:library/alpine:pull")
    }

    func testParsesUnquotedAndSpacedParameters() throws {
        let challenge = try XCTUnwrap(
            BearerChallenge.parse("bearer realm=https://auth.example.com/token, service=example")
        )
        XCTAssertEqual(challenge.realm, "https://auth.example.com/token")
        XCTAssertEqual(challenge.service, "example")
        XCTAssertNil(challenge.scope)
    }

    func testIgnoresNonBearerSchemes() {
        XCTAssertNil(BearerChallenge.parse(#"Basic realm="registry""#))
    }

    func testTokenURLCarriesServiceAndScope() throws {
        let challenge = BearerChallenge(
            realm: "https://auth.docker.io/token",
            service: "registry.docker.io",
            scope: nil
        )
        let url = try XCTUnwrap(challenge.tokenURL(fallbackScope: "repository:library/alpine:pull"))
        let components = try XCTUnwrap(URLComponents(url: url, resolvingAgainstBaseURL: false))
        let items = Dictionary(
            uniqueKeysWithValues: (components.queryItems ?? []).map { ($0.name, $0.value ?? "") }
        )
        XCTAssertEqual(items["service"], "registry.docker.io")
        XCTAssertEqual(items["scope"], "repository:library/alpine:pull")
    }
}

/// Records every URL the client asks for so tests can assert on the flow.
private final class RequestLog {
    private(set) var urls: [String] = []
    func record(_ url: String) { urls.append(url) }
}

private struct StubTransport: HTTPTransport {
    var bodies: [String: (data: Data, contentType: String)]
    var requireAuthorization: Bool
    var log: RequestLog

    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse) {
        guard let url = request.url else { throw RegistryError.notHTTP }
        log.record(url.absoluteString)

        if url.host == "auth.example.com" {
            let token = Data(#"{"token":"stub-token"}"#.utf8)
            return (token, response(url, 200, ["Content-Type": "application/json"]))
        }

        if requireAuthorization, request.value(forHTTPHeaderField: "Authorization") == nil {
            let header = #"Bearer realm="https://auth.example.com/token",service="registry.example.com""#
            return (Data(), response(url, 401, ["WWW-Authenticate": header]))
        }

        guard let body = bodies[url.path] else {
            return (Data("no such route".utf8), response(url, 404, [:]))
        }
        return (body.data, response(url, 200, ["Content-Type": body.contentType]))
    }

    private func response(_ url: URL, _ status: Int, _ headers: [String: String]) -> HTTPURLResponse {
        HTTPURLResponse(url: url, statusCode: status, httpVersion: "HTTP/1.1", headerFields: headers)!
    }
}

final class ContainerLabRegistryClientTests: XCTestCase {
    private struct Fixture {
        var reference: ImageReference
        var bodies: [String: (data: Data, contentType: String)]
        var manifestDigest: String
        var configDigest: String
    }

    private func makeFixture() throws -> Fixture {
        let reference = try ImageReference(parsing: "registry.example.com/team/app:1.0")

        let config = OCIImageConfig(
            architecture: "arm64",
            os: "linux",
            variant: nil,
            config: OCIImageConfig.RunConfig(
                entrypoint: ["/bin/sh"],
                cmd: ["-c", "echo hi"],
                env: nil,
                workingDir: nil,
                user: nil
            ),
            rootfs: OCIImageConfig.RootFS(type: "layers", diffIDs: [])
        )
        let configData = try JSONEncoder().encode(config)
        let configDigest = OCIDigest.sha256(of: configData)

        let manifest = OCIManifest(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociManifest,
            config: OCIDescriptor(
                mediaType: OCIMediaType.ociConfig,
                digest: configDigest,
                size: Int64(configData.count),
                platform: nil,
                annotations: nil
            ),
            layers: [
                OCIDescriptor(
                    mediaType: OCIMediaType.ociLayerGzip,
                    digest: OCIDigest.sha256(of: Data("layer".utf8)),
                    size: 5,
                    platform: nil,
                    annotations: nil
                )
            ],
            annotations: nil
        )
        let manifestData = try ImageLayout.encoder.encode(manifest)
        let manifestDigest = OCIDigest.sha256(of: manifestData)

        let index = OCIIndex(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociIndex,
            manifests: [
                OCIDescriptor(
                    mediaType: OCIMediaType.ociManifest,
                    digest: OCIDigest.sha256(of: Data("amd64-manifest".utf8)),
                    size: 10,
                    platform: OCIPlatform(architecture: "amd64", os: "linux", variant: nil),
                    annotations: nil
                ),
                OCIDescriptor(
                    mediaType: OCIMediaType.ociManifest,
                    digest: manifestDigest,
                    size: Int64(manifestData.count),
                    platform: OCIPlatform(architecture: "arm64", os: "linux", variant: "v8"),
                    annotations: nil
                )
            ]
        )
        let indexData = try ImageLayout.encoder.encode(index)

        let bodies: [String: (data: Data, contentType: String)] = [
            "/v2/team/app/manifests/1.0": (indexData, OCIMediaType.ociIndex),
            "/v2/team/app/manifests/\(manifestDigest)": (manifestData, OCIMediaType.ociManifest),
            "/v2/team/app/blobs/\(configDigest)": (configData, OCIMediaType.ociConfig)
        ]

        return Fixture(
            reference: reference,
            bodies: bodies,
            manifestDigest: manifestDigest,
            configDigest: configDigest
        )
    }

    func testResolvesIndexToRequestedPlatform() async throws {
        let fixture = try makeFixture()
        let log = RequestLog()
        let client = RegistryClient(
            transport: StubTransport(bodies: fixture.bodies, requireAuthorization: false, log: log)
        )

        let resolved = try await client.resolve(fixture.reference, platform: .linuxArm64)

        XCTAssertEqual(resolved.manifestDescriptor.digest, fixture.manifestDigest)
        XCTAssertEqual(resolved.platform.architecture, "arm64")
        XCTAssertEqual(resolved.config.commandLine, ["/bin/sh", "-c", "echo hi"])
        XCTAssertEqual(resolved.manifest.layers.count, 1)
    }

    func testAnonymousTokenFlowRetriesWithBearer() async throws {
        let fixture = try makeFixture()
        let log = RequestLog()
        let client = RegistryClient(
            transport: StubTransport(bodies: fixture.bodies, requireAuthorization: true, log: log)
        )

        _ = try await client.resolve(fixture.reference, platform: .linuxArm64)

        XCTAssertTrue(
            log.urls.contains { $0.hasPrefix("https://auth.example.com/token") },
            "Expected the client to follow the WWW-Authenticate challenge: \(log.urls)"
        )
        // One 401, one token fetch, one retry — the token is then reused for the
        // child manifest and the config blob rather than re-challenged.
        let tokenRequests = log.urls.filter { $0.hasPrefix("https://auth.example.com/token") }
        XCTAssertEqual(tokenRequests.count, 1)
    }

    func testMissingPlatformIsReported() async throws {
        let fixture = try makeFixture()
        let client = RegistryClient(
            transport: StubTransport(bodies: fixture.bodies, requireAuthorization: false, log: RequestLog())
        )

        do {
            _ = try await client.resolve(
                fixture.reference,
                platform: OCIPlatform(architecture: "riscv64", os: "linux", variant: nil)
            )
            XCTFail("Expected a missing-platform error")
        } catch let error as RegistryError {
            guard case .noMatchingPlatform = error else {
                return XCTFail("Unexpected registry error: \(error)")
            }
        }
    }

    func testBlobDigestIsVerified() async throws {
        let fixture = try makeFixture()
        var bodies = fixture.bodies
        let tamperedDigest = OCIDigest.sha256(of: Data("expected".utf8))
        bodies["/v2/team/app/blobs/\(tamperedDigest)"] = (Data("tampered".utf8), "application/octet-stream")
        let client = RegistryClient(
            transport: StubTransport(bodies: bodies, requireAuthorization: false, log: RequestLog())
        )

        let descriptor = OCIDescriptor(
            mediaType: OCIMediaType.ociLayerTar,
            digest: tamperedDigest,
            size: 8,
            platform: nil,
            annotations: nil
        )

        do {
            _ = try await client.fetchBlob(descriptor, from: fixture.reference)
            XCTFail("Expected a digest mismatch")
        } catch let error as OCIDigestError {
            guard case .mismatch = error else {
                return XCTFail("Unexpected digest error: \(error)")
            }
        }
    }

    func testHTTPErrorsSurface() async throws {
        let client = RegistryClient(
            transport: StubTransport(bodies: [:], requireAuthorization: false, log: RequestLog())
        )

        do {
            _ = try await client.resolve(try ImageReference(parsing: "registry.example.com/nope:1"), platform: .linuxArm64)
            XCTFail("Expected an HTTP error")
        } catch let error as RegistryError {
            guard case .badStatus(let code, _) = error else {
                return XCTFail("Unexpected registry error: \(error)")
            }
            XCTAssertEqual(code, 404)
        }
    }
}

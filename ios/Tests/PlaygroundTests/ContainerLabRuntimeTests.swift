import XCTest
@testable import Playground

final class ContainerLabHTTPTests: XCTestCase {
    func testParsesRequestLineAndQuery() throws {
        let head = "GET /image/blobs/sha256/abc?mode=run&debug HTTP/1.1\r\nHost: 127.0.0.1\r\nAccept: */*"
        let request = try XCTUnwrap(LoopbackServer.parseRequest(head))

        XCTAssertEqual(request.method, "GET")
        XCTAssertEqual(request.path, "/image/blobs/sha256/abc")
        XCTAssertEqual(request.query["mode"], "run")
        XCTAssertEqual(request.query["debug"], "")
        XCTAssertEqual(request.headers["host"], "127.0.0.1")
    }

    func testRejectsGarbageRequestLine() {
        XCTAssertNil(LoopbackServer.parseRequest("nonsense"))
    }

    func testEveryResponseCarriesIsolationHeaders() {
        let serialized = LoopbackServer.serialize(.text("hi"))
        let text = String(decoding: serialized, as: UTF8.self)

        XCTAssertTrue(text.hasPrefix("HTTP/1.1 200 OK\r\n"))
        XCTAssertTrue(text.contains("Cross-Origin-Opener-Policy: same-origin\r\n"))
        XCTAssertTrue(text.contains("Cross-Origin-Embedder-Policy: require-corp\r\n"))
        XCTAssertTrue(text.contains("Cross-Origin-Resource-Policy: same-origin\r\n"))
        XCTAssertTrue(text.contains("Content-Length: 2\r\n"))
        XCTAssertTrue(text.hasSuffix("\r\n\r\nhi"))
    }

    func testHeaderTerminatorIsFound() {
        let data = Data("GET / HTTP/1.1\r\nHost: x\r\n\r\nbody".utf8)
        XCTAssertEqual(LoopbackServer.headerTerminator(in: data), 23)
        XCTAssertNil(LoopbackServer.headerTerminator(in: Data("GET / HTTP/1.1\r\n".utf8)))
    }

    func testWasmGetsItsOwnContentType() {
        XCTAssertEqual(LoopbackServer.contentType(forPathExtension: "wasm"), "application/wasm")
        XCTAssertEqual(LoopbackServer.contentType(forPathExtension: "HTML"), "text/html; charset=utf-8")
        XCTAssertEqual(LoopbackServer.contentType(forPathExtension: ""), "application/octet-stream")
    }

    func testPathTraversalIsRefused() throws {
        let root = FileManager.default.temporaryDirectory
            .appendingPathComponent("container-lab-root-\(UUID().uuidString)", isDirectory: true)
        try FileManager.default.createDirectory(at: root, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: root) }

        XCTAssertNotNil(
            ContainerRuntimeServer.resolvedFileURL(relativePath: "blobs/sha256/abc", under: root)
        )
        XCTAssertNil(ContainerRuntimeServer.resolvedFileURL(relativePath: "../secrets", under: root))
        XCTAssertNil(ContainerRuntimeServer.resolvedFileURL(relativePath: "a/../../b", under: root))
        XCTAssertNil(ContainerRuntimeServer.resolvedFileURL(relativePath: "", under: root))
    }
}

/// Exercises the real loopback listener in the simulator. These are the tests
/// that prove the runtime plan is viable on this platform rather than just on
/// paper.
final class ContainerLabLoopbackServerTests: XCTestCase {
    private var server: ContainerRuntimeServer!
    private var imageRoot: URL!

    override func setUpWithError() throws {
        server = ContainerRuntimeServer()
        imageRoot = FileManager.default.temporaryDirectory
            .appendingPathComponent("container-lab-serve-\(UUID().uuidString)", isDirectory: true)
        try FileManager.default.createDirectory(at: imageRoot, withIntermediateDirectories: true)
    }

    override func tearDownWithError() throws {
        server?.stop()
        server = nil
        try? FileManager.default.removeItem(at: imageRoot)
    }

    private func session() -> URLSession {
        let configuration = URLSessionConfiguration.ephemeral
        configuration.requestCachePolicy = .reloadIgnoringLocalAndRemoteCacheData
        return URLSession(configuration: configuration)
    }

    func testServesProbePageOverLoopbackWithIsolationHeaders() async throws {
        let base = try await server.start(imageRoot: imageRoot)
        XCTAssertEqual(base.host, "127.0.0.1")

        let (data, response) = try await session().data(from: base.appendingPathComponent("probe.html"))
        let http = try XCTUnwrap(response as? HTTPURLResponse)

        XCTAssertEqual(http.statusCode, 200)
        XCTAssertEqual(http.value(forHTTPHeaderField: "Cross-Origin-Opener-Policy"), "same-origin")
        XCTAssertEqual(http.value(forHTTPHeaderField: "Cross-Origin-Embedder-Policy"), "require-corp")
        XCTAssertEqual(http.value(forHTTPHeaderField: "Cross-Origin-Resource-Policy"), "same-origin")
        XCTAssertTrue(String(decoding: data, as: UTF8.self).contains("<!doctype html>"))
    }

    func testServesImageLayoutBlobs() async throws {
        let layout = ImageLayout(root: imageRoot)
        try layout.prepare()
        let payload = Data("a fake layer".utf8)
        let digest = OCIDigest.sha256(of: payload)
        try layout.writeBlob(payload, digest: digest)
        try layout.writeIndex(
            manifest: OCIDescriptor(
                mediaType: OCIMediaType.ociManifest,
                digest: digest,
                size: Int64(payload.count),
                platform: .linuxArm64,
                annotations: nil
            ),
            refName: "alpine:3.20"
        )

        let base = try await server.start(imageRoot: imageRoot)
        let hex = try XCTUnwrap(OCIDigest.hex(digest))

        let (blob, blobResponse) = try await session().data(
            from: base.appendingPathComponent("image/blobs/sha256/\(hex)")
        )
        XCTAssertEqual((blobResponse as? HTTPURLResponse)?.statusCode, 200)
        XCTAssertEqual(blob, payload)

        let (indexData, indexResponse) = try await session().data(
            from: base.appendingPathComponent("image/index.json")
        )
        XCTAssertEqual((indexResponse as? HTTPURLResponse)?.statusCode, 200)
        XCTAssertEqual(
            (indexResponse as? HTTPURLResponse)?.value(forHTTPHeaderField: "Content-Type"),
            "application/json"
        )
        let index = try JSONDecoder().decode(OCIIndex.self, from: indexData)
        XCTAssertEqual(index.manifests.first?.digest, digest)
    }

    func testUnknownPathIs404() async throws {
        let base = try await server.start(imageRoot: imageRoot)
        let (_, response) = try await session().data(from: base.appendingPathComponent("nope.txt"))
        XCTAssertEqual((response as? HTTPURLResponse)?.statusCode, 404)
    }
}

/// The go/no-go check for the whole design: is a `WKWebView` page served from
/// our loopback origin cross-origin isolated? Without this there is no
/// `SharedArrayBuffer`, no wasm threads, and no emulator.
@MainActor
final class ContainerLabIsolationProbeTests: XCTestCase {
    func testLoopbackOriginIsCrossOriginIsolatedInWKWebView() async throws {
        let server = ContainerRuntimeServer()
        defer { server.stop() }
        let base = try await server.start()

        let probe = CrossOriginIsolationProbe()
        let result = try await probe.run(url: base.appendingPathComponent("probe.html"), timeout: 30)

        XCTAssertTrue(result.webAssembly, "WebAssembly missing: \(result.summary)")
        XCTAssertTrue(result.crossOriginIsolated, "Not cross-origin isolated: \(result.summary)")
        XCTAssertTrue(result.sharedArrayBuffer, "No SharedArrayBuffer: \(result.summary)")
        XCTAssertTrue(result.sharedMemory, "No shared wasm memory: \(result.summary)")
        XCTAssertTrue(result.isRuntimeCapable)
    }
}

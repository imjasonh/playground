import XCTest

@testable import Playground

/// The host-side pieces that need no wasm: framing requests off a socket,
/// finding the module inside an OCI artifact, caching it, and working out
/// which address to show the user.
final class WasmServiceHostTests: XCTestCase {
    // MARK: - Framing

    func testHeadersOnlyRequestIsCompleteAtTheBlankLine() {
        let request = Data("GET / HTTP/1.1\r\nHost: phone\r\n\r\n".utf8)
        XCTAssertEqual(
            HTTPRequestFramer.examine(request, maximumBodyBytes: 1024),
            .complete(byteCount: request.count)
        )
    }

    func testPartialHeadersAskForMore() {
        let request = Data("GET / HTTP/1.1\r\nHost: pho".utf8)
        XCTAssertEqual(HTTPRequestFramer.examine(request, maximumBodyBytes: 1024), .needMore)
    }

    func testBodyIsWaitedForAndThenFramedExactly() {
        let head = "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\n"
        XCTAssertEqual(
            HTTPRequestFramer.examine(Data((head + "hel").utf8), maximumBodyBytes: 1024),
            .needMore
        )
        XCTAssertEqual(
            HTTPRequestFramer.examine(Data((head + "hello").utf8), maximumBodyBytes: 1024),
            .complete(byteCount: head.utf8.count + 5)
        )
    }

    /// A pipelined second request must not be swallowed into the first.
    func testFramingStopsAtTheEndOfTheFirstRequest() {
        let first = "POST / HTTP/1.1\r\nContent-Length: 2\r\n\r\nhi"
        let buffer = Data((first + "GET /next HTTP/1.1\r\n\r\n").utf8)
        XCTAssertEqual(
            HTTPRequestFramer.examine(buffer, maximumBodyBytes: 1024),
            .complete(byteCount: first.utf8.count)
        )
    }

    func testOversizedBodyIsRefusedBeforeItArrives() {
        let request = Data("POST / HTTP/1.1\r\nContent-Length: 99999\r\n\r\n".utf8)
        guard case .refuse(let status, _) = HTTPRequestFramer.examine(request, maximumBodyBytes: 1024) else {
            return XCTFail("an oversized body should be refused")
        }
        XCTAssertEqual(status, 413)
    }

    func testNonNumericContentLengthIsRefused() {
        let request = Data("POST / HTTP/1.1\r\nContent-Length: soon\r\n\r\n".utf8)
        guard case .refuse(let status, _) = HTTPRequestFramer.examine(request, maximumBodyBytes: 1024) else {
            return XCTFail("a bad Content-Length should be refused")
        }
        XCTAssertEqual(status, 400)
    }

    /// De-chunking would have to happen before the guest sees the bytes, and
    /// nothing does it — so say so rather than hand over an unreadable body.
    func testChunkedRequestIsRefused() {
        let request = Data("POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n".utf8)
        guard case .refuse(let status, _) = HTTPRequestFramer.examine(request, maximumBodyBytes: 1024) else {
            return XCTFail("a chunked body should be refused")
        }
        XCTAssertEqual(status, 501)
    }

    func testEndlessHeadersAreRefusedRatherThanBuffered() {
        let request = Data(("GET / HTTP/1.1\r\nX: " + String(repeating: "a", count: 70_000)).utf8)
        guard case .refuse(let status, _) = HTTPRequestFramer.examine(request, maximumBodyBytes: 1024) else {
            return XCTFail("unbounded headers should be refused")
        }
        XCTAssertEqual(status, 431)
    }

    /// `Data` off a connection can carry non-zero indices; framing must count
    /// from the buffer's own start.
    func testFramingHandlesASlicedBuffer() {
        let padded = Data(repeating: 0, count: 8) + Data("GET / HTTP/1.1\r\n\r\n".utf8)
        let sliced = padded.dropFirst(8)
        XCTAssertEqual(
            HTTPRequestFramer.examine(sliced, maximumBodyBytes: 1024),
            .complete(byteCount: sliced.count)
        )
    }

    func testRefusalIsAWellFormedResponse() {
        let response = String(decoding: HTTPRequestFramer.refusal(status: 413, reason: "too big"), as: UTF8.self)
        XCTAssertTrue(response.hasPrefix("HTTP/1.1 413 Content Too Large\r\n"))
        XCTAssertTrue(response.contains("Content-Length: 8\r\n"))
        XCTAssertTrue(response.hasSuffix("\r\n\r\ntoo big\n"))
    }

    // MARK: - Finding the module in an artifact

    func testWasmLayerIsFoundByMediaType() throws {
        let manifest = manifest(layers: [
            descriptor("application/vnd.oci.image.layer.v1.tar+gzip", digest: "sha256:aa"),
            descriptor("application/wasm", digest: "sha256:bb"),
        ])
        XCTAssertEqual(try WasmArtifact.moduleLayer(in: manifest).digest, "sha256:bb")
    }

    func testWasmLayerIsFoundBySuffix() throws {
        let manifest = manifest(layers: [
            descriptor("application/vnd.module.wasm.content.layer.v1+wasm", digest: "sha256:cc")
        ])
        XCTAssertEqual(try WasmArtifact.moduleLayer(in: manifest).digest, "sha256:cc")
    }

    /// `oras push` labels the layer whatever you tell it to, and people tell it
    /// nothing. A single blob under a wasm artifact type is unambiguous anyway.
    func testSingleLayerUnderAWasmArtifactTypeIsAccepted() throws {
        var manifest = manifest(layers: [descriptor("application/octet-stream", digest: "sha256:dd")])
        manifest.artifactType = "application/vnd.wasm.config.v0+json"
        XCTAssertEqual(try WasmArtifact.moduleLayer(in: manifest).digest, "sha256:dd")
    }

    func testLayerNamedDotWasmIsAccepted() throws {
        var layer = descriptor("application/octet-stream", digest: "sha256:ee")
        layer.annotations = ["org.opencontainers.image.title": "hello.wasm"]
        XCTAssertEqual(try WasmArtifact.moduleLayer(in: manifest(layers: [layer])).digest, "sha256:ee")
    }

    /// Pointing this at `alpine:3.20` should say what is wrong, not fail
    /// halfway through instantiating a tarball.
    func testContainerImageIsRejectedWithAnExplanation() {
        let manifest = manifest(layers: [
            descriptor("application/vnd.oci.image.layer.v1.tar+gzip", digest: "sha256:aa"),
            descriptor("application/vnd.oci.image.layer.v1.tar+gzip", digest: "sha256:bb"),
        ])
        XCTAssertThrowsError(try WasmArtifact.moduleLayer(in: manifest)) { error in
            XCTAssertTrue(
                error.localizedDescription.contains("not a container image"),
                "unhelpful message: \(error.localizedDescription)"
            )
        }
    }

    // MARK: - Cache

    func testDigestBecomesASafeFileName() {
        XCTAssertEqual(
            WasmModuleStore.fileName(forDigest: "sha256:abc123"),
            "abc123.wasm"
        )
        XCTAssertEqual(WasmModuleStore.fileName(forDigest: "nonsense"), "module.wasm")
    }

    func testModuleSurvivesARoundTripThroughTheCache() throws {
        let store = WasmModuleStore()
        let digest = "sha256:" + String(repeating: "a", count: 64)
        let module = Data("not really wasm".utf8)

        let url = try store.save(module, digest: digest)
        addTeardownBlock { try? FileManager.default.removeItem(at: url) }
        XCTAssertEqual(store.load(digest: digest), module)
    }

    func testLastRecordRoundTrips() throws {
        let defaults = try XCTUnwrap(UserDefaults(suiteName: "wasmservice.tests.\(UUID().uuidString)"))
        let store = WasmModuleStore(defaults: defaults)
        let record = WasmModuleStore.Record(reference: "ghcr.io/x/y:latest", digest: "sha256:ab", port: 9090)

        store.lastRecord = record
        XCTAssertEqual(store.lastRecord, record)
    }

    // MARK: - Addresses

    /// A tunnel is the interesting one once a tailnet exists, and loopback is
    /// last because it only works from the phone itself.
    func testAddressesAreOrderedByUsefulness() {
        let sorted = LocalAddresses.sorted([
            LocalAddresses.Interface(name: "lo0", address: "127.0.0.1"),
            LocalAddresses.Interface(name: "en0", address: "192.168.1.20"),
            LocalAddresses.Interface(name: "utun4", address: "100.101.102.103"),
        ])
        XCTAssertEqual(sorted.map(\.name), ["utun4", "en0", "lo0"])
        XCTAssertEqual(
            sorted.map(\.kind),
            ["tailnet — reachable anywhere", "Wi-Fi", "this device"]
        )
    }

    /// Tailscale's 100.64.0.0/10 is what distinguishes a tailnet from a
    /// corporate VPN, and both arrive as `utun`.
    func testOnlyCGNATTunnelsAreCalledTailnets() {
        XCTAssertTrue(
            LocalAddresses.Interface(name: "utun3", address: "100.127.255.254").isTailnet
        )
        XCTAssertFalse(
            LocalAddresses.Interface(name: "utun3", address: "10.8.0.2").isTailnet,
            "a plain VPN tunnel is not a tailnet"
        )
        XCTAssertFalse(
            LocalAddresses.Interface(name: "utun3", address: "100.128.0.1").isTailnet,
            "100.128/9 is outside the CGNAT range"
        )
        XCTAssertFalse(
            LocalAddresses.Interface(name: "en0", address: "100.64.0.1").isTailnet,
            "a tailnet address only counts on a tunnel interface"
        )
    }

    // MARK: - Helpers

    private func descriptor(_ mediaType: String, digest: String) -> OCIDescriptor {
        OCIDescriptor(mediaType: mediaType, digest: digest, size: 1, platform: nil, annotations: nil)
    }

    private func manifest(layers: [OCIDescriptor]) -> OCIManifest {
        OCIManifest(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociManifest,
            artifactType: nil,
            config: descriptor("application/vnd.oci.empty.v1+json", digest: "sha256:00"),
            layers: layers,
            annotations: nil
        )
    }
}

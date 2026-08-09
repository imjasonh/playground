import XCTest
@testable import Playground

final class ContainerLabImageReferenceTests: XCTestCase {
    func testBareNameGetsDockerHubDefaults() throws {
        let reference = try ImageReference(parsing: "alpine")
        XCTAssertEqual(reference.registryHost, "registry-1.docker.io")
        XCTAssertEqual(reference.displayHost, "docker.io")
        XCTAssertEqual(reference.repository, "library/alpine")
        XCTAssertEqual(reference.tag, "latest")
        XCTAssertNil(reference.digest)
        XCTAssertEqual(reference.canonicalName, "alpine:latest")
    }

    func testTagIsParsed() throws {
        let reference = try ImageReference(parsing: "alpine:3.20")
        XCTAssertEqual(reference.repository, "library/alpine")
        XCTAssertEqual(reference.tag, "3.20")
        XCTAssertEqual(reference.apiReference, "3.20")
    }

    func testNamespacedDockerHubImageKeepsItsNamespace() throws {
        let reference = try ImageReference(parsing: "arm64v8/alpine:3.20")
        XCTAssertEqual(reference.repository, "arm64v8/alpine")
        XCTAssertEqual(reference.canonicalName, "arm64v8/alpine:3.20")
    }

    func testExplicitRegistry() throws {
        let reference = try ImageReference(parsing: "ghcr.io/imjasonh/playground:v1")
        XCTAssertEqual(reference.registryHost, "ghcr.io")
        XCTAssertEqual(reference.repository, "imjasonh/playground")
        XCTAssertEqual(reference.tag, "v1")
        XCTAssertEqual(reference.canonicalName, "ghcr.io/imjasonh/playground:v1")
    }

    func testRegistryPortIsNotATag() throws {
        let reference = try ImageReference(parsing: "localhost:5000/team/app:dev")
        XCTAssertEqual(reference.registryHost, "localhost:5000")
        XCTAssertEqual(reference.repository, "team/app")
        XCTAssertEqual(reference.tag, "dev")
    }

    func testDigestWins() throws {
        let digest = "sha256:" + String(repeating: "a", count: 64)
        let reference = try ImageReference(parsing: "alpine@\(digest)")
        XCTAssertEqual(reference.digest, digest)
        XCTAssertNil(reference.tag)
        XCTAssertEqual(reference.apiReference, digest)
        XCTAssertEqual(reference.canonicalName, "alpine@\(digest)")
    }

    func testIndexDockerIOIsNormalized() throws {
        let reference = try ImageReference(parsing: "index.docker.io/library/alpine:3.20")
        XCTAssertEqual(reference.registryHost, "registry-1.docker.io")
        XCTAssertEqual(reference.canonicalName, "alpine:3.20")
    }

    func testRejectsGarbage() {
        XCTAssertThrowsError(try ImageReference(parsing: ""))
        XCTAssertThrowsError(try ImageReference(parsing: "Alpine"))
        XCTAssertThrowsError(try ImageReference(parsing: "alpine@sha256:nope"))
    }
}

final class ContainerLabDigestTests: XCTestCase {
    func testSHA256MatchesKnownVector() {
        let digest = OCIDigest.sha256(of: Data("hello".utf8))
        XCTAssertEqual(
            digest,
            "sha256:2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        )
    }

    func testValidation() {
        XCTAssertTrue(OCIDigest.isValid("sha256:" + String(repeating: "0", count: 64)))
        XCTAssertFalse(OCIDigest.isValid("sha256:" + String(repeating: "0", count: 63)))
        XCTAssertFalse(OCIDigest.isValid("sha512:" + String(repeating: "0", count: 64)))
        XCTAssertFalse(OCIDigest.isValid("sha256:" + String(repeating: "A", count: 64)))
    }

    func testVerifyThrowsOnMismatch() {
        let wrong = "sha256:" + String(repeating: "b", count: 64)
        XCTAssertThrowsError(try OCIDigest.verify(Data("hello".utf8), matches: wrong))
    }
}

final class ContainerLabPlatformMatcherTests: XCTestCase {
    private func descriptor(_ os: String, _ architecture: String, variant: String? = nil) -> OCIDescriptor {
        OCIDescriptor(
            mediaType: OCIMediaType.ociManifest,
            digest: OCIDigest.sha256(of: Data("\(os)/\(architecture)/\(variant ?? "")".utf8)),
            size: 1,
            platform: OCIPlatform(architecture: architecture, os: os, variant: variant),
            annotations: nil
        )
    }

    func testPicksRequestedArchitecture() {
        let index = OCIIndex(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociIndex,
            manifests: [descriptor("linux", "amd64"), descriptor("linux", "arm64", variant: "v8")]
        )
        let selected = PlatformMatcher.select(from: index, matching: .linuxArm64)
        XCTAssertEqual(selected?.platform?.architecture, "arm64")
    }

    func testTreatsArm64V8AsPlainArm64() {
        let index = OCIIndex(
            schemaVersion: 2,
            mediaType: nil,
            manifests: [descriptor("linux", "arm64", variant: "v8")]
        )
        XCTAssertNotNil(PlatformMatcher.select(from: index, matching: .linuxArm64))
    }

    func testSkipsAttestationEntries() {
        let index = OCIIndex(
            schemaVersion: 2,
            mediaType: nil,
            manifests: [descriptor("unknown", "unknown"), descriptor("linux", "arm64")]
        )
        let selected = PlatformMatcher.select(from: index, matching: .linuxArm64)
        XCTAssertEqual(selected?.platform?.os, "linux")
    }

    func testReturnsNilWhenPlatformIsAbsent() {
        let index = OCIIndex(schemaVersion: 2, mediaType: nil, manifests: [descriptor("linux", "riscv64")])
        XCTAssertNil(PlatformMatcher.select(from: index, matching: .linuxArm64))
    }
}

final class ContainerLabGunzipTests: XCTestCase {
    /// gzip of "hello from container lab\n" repeated 40 times (1000 bytes).
    private static let fixtureBase64 =
        "H4sIAAAAAAAAA8tIzcnJV0grys9VSM7PK0nMzEstUshJTOLKGJUYlRiVGC4SAErZxxPoAwAA"
    private static let fixtureDigest =
        "sha256:7e6b2476873dafd6467749a41736d399d9311c9dfdc047c8cedca4d5de4e0e14"

    func testDetectsGzipMagic() throws {
        let data = try XCTUnwrap(Data(base64Encoded: Self.fixtureBase64))
        XCTAssertTrue(Gunzip.isGzip(data))
        XCTAssertFalse(Gunzip.isGzip(Data("not gzip".utf8)))
    }

    func testDecompressesToExpectedBytes() throws {
        let data = try XCTUnwrap(Data(base64Encoded: Self.fixtureBase64))
        let inflated = try Gunzip.decompress(data)
        XCTAssertEqual(inflated.count, 1000)
        XCTAssertEqual(OCIDigest.sha256(of: inflated), Self.fixtureDigest)
        XCTAssertEqual(
            String(decoding: inflated.prefix(24), as: UTF8.self),
            "hello from container lab"
        )
    }

    func testDecompressesEmptyMember() throws {
        let data = try XCTUnwrap(Data(base64Encoded: "H4sIAAAAAAAAAwMAAAAAAAAAAAA="))
        XCTAssertEqual(try Gunzip.decompress(data).count, 0)
    }

    func testRejectsNonGzip() {
        XCTAssertThrowsError(try Gunzip.decompress(Data(repeating: 7, count: 64)))
    }
}

final class ContainerLabImageLayoutTests: XCTestCase {
    private var root: URL!

    override func setUpWithError() throws {
        root = FileManager.default.temporaryDirectory
            .appendingPathComponent("container-lab-tests-\(UUID().uuidString)", isDirectory: true)
    }

    override func tearDownWithError() throws {
        try? FileManager.default.removeItem(at: root)
    }

    func testPrepareWritesLayoutMarker() throws {
        let layout = ImageLayout(root: root)
        try layout.prepare()

        let marker = root.appendingPathComponent("oci-layout")
        let json = try JSONSerialization.jsonObject(with: Data(contentsOf: marker)) as? [String: String]
        XCTAssertEqual(json?["imageLayoutVersion"], "1.0.0")
        var isDirectory: ObjCBool = false
        XCTAssertTrue(
            FileManager.default.fileExists(atPath: layout.blobsDirectory.path, isDirectory: &isDirectory)
        )
        XCTAssertTrue(isDirectory.boolValue)
    }

    func testBlobsAreStoredByDigestHex() throws {
        let layout = ImageLayout(root: root)
        try layout.prepare()
        let payload = Data("blob".utf8)
        let digest = OCIDigest.sha256(of: payload)

        let url = try layout.writeBlob(payload, digest: digest)

        XCTAssertEqual(url.lastPathComponent, try XCTUnwrap(OCIDigest.hex(digest)))
        XCTAssertEqual(try Data(contentsOf: url), payload)
    }

    func testIndexRecordsRefName() throws {
        let layout = ImageLayout(root: root)
        try layout.prepare()
        let descriptor = OCIDescriptor(
            mediaType: OCIMediaType.ociManifest,
            digest: OCIDigest.sha256(of: Data("manifest".utf8)),
            size: 8,
            platform: .linuxArm64,
            annotations: nil
        )

        try layout.writeIndex(manifest: descriptor, refName: "alpine:3.20")

        let index = try layout.readIndex()
        XCTAssertEqual(index.manifests.count, 1)
        XCTAssertEqual(index.manifests[0].digest, descriptor.digest)
        XCTAssertEqual(
            index.manifests[0].annotations?[ImageLayout.refNameAnnotation],
            "alpine:3.20"
        )
    }
}

final class ContainerLabMaterializerTests: XCTestCase {
    private var root: URL!

    /// Same gzip fixture as the gunzip tests: 1000 bytes of known content.
    private static let layerGzipBase64 =
        "H4sIAAAAAAAAA8tIzcnJV0grys9VSM7PK0nMzEstUshJTOLKGJUYlRiVGC4SAErZxxPoAwAA"
    private static let layerDiffID =
        "sha256:7e6b2476873dafd6467749a41736d399d9311c9dfdc047c8cedca4d5de4e0e14"

    override func setUpWithError() throws {
        root = FileManager.default.temporaryDirectory
            .appendingPathComponent("container-lab-materialize-\(UUID().uuidString)", isDirectory: true)
    }

    override func tearDownWithError() throws {
        try? FileManager.default.removeItem(at: root)
    }

    private func makeResolved(diffIDs: [String]) throws -> (ResolvedImage, Data) {
        let gzip = try XCTUnwrap(Data(base64Encoded: Self.layerGzipBase64))
        let config = OCIImageConfig(
            architecture: "arm64",
            os: "linux",
            variant: nil,
            config: OCIImageConfig.RunConfig(
                entrypoint: nil,
                cmd: ["/bin/sh"],
                env: ["PATH=/usr/bin"],
                workingDir: "/",
                user: nil
            ),
            rootfs: OCIImageConfig.RootFS(type: "layers", diffIDs: diffIDs)
        )
        let configData = try JSONEncoder().encode(config)
        let layer = OCIDescriptor(
            mediaType: OCIMediaType.dockerLayerGzip,
            digest: OCIDigest.sha256(of: gzip),
            size: Int64(gzip.count),
            platform: nil,
            annotations: nil
        )
        let manifest = OCIManifest(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociManifest,
            config: OCIDescriptor(
                mediaType: OCIMediaType.ociConfig,
                digest: OCIDigest.sha256(of: configData),
                size: Int64(configData.count),
                platform: nil,
                annotations: nil
            ),
            layers: [layer],
            annotations: nil
        )
        let manifestData = try ImageLayout.encoder.encode(manifest)

        let resolved = ResolvedImage(
            reference: try ImageReference(parsing: "alpine:3.20"),
            manifestDescriptor: OCIDescriptor(
                mediaType: OCIMediaType.ociManifest,
                digest: OCIDigest.sha256(of: manifestData),
                size: Int64(manifestData.count),
                platform: .linuxArm64,
                annotations: nil
            ),
            manifestData: manifestData,
            manifest: manifest,
            configData: configData,
            config: config
        )
        return (resolved, gzip)
    }

    func testDecompressedLayerDigestEqualsDiffID() async throws {
        let (resolved, gzip) = try makeResolved(diffIDs: [Self.layerDiffID])

        let result = try await ImageMaterializer.materialize(
            resolved,
            into: root,
            decompressLayers: true,
            fetchBlob: { descriptor in
                descriptor.mediaType == OCIMediaType.ociConfig ? resolved.configData : gzip
            }
        )

        XCTAssertEqual(result.layerCount, 1)
        XCTAssertEqual(result.decompressedLayerCount, 1)
        XCTAssertEqual(result.platform.architecture, "arm64")
        XCTAssertEqual(result.commandLine, ["/bin/sh"])

        // The inflated layer is stored under the diff_id, which is what makes
        // the rewritten manifest verifiable against the original config.
        let layout = ImageLayout(root: root)
        let inflatedURL = try layout.blobURL(for: Self.layerDiffID)
        XCTAssertTrue(FileManager.default.fileExists(atPath: inflatedURL.path))
        XCTAssertEqual(try Data(contentsOf: inflatedURL).count, 1000)

        let index = try layout.readIndex()
        let manifestData = try Data(contentsOf: layout.blobURL(for: index.manifests[0].digest))
        let manifest = try JSONDecoder().decode(OCIManifest.self, from: manifestData)
        XCTAssertEqual(manifest.layers[0].mediaType, OCIMediaType.ociLayerTar)
        XCTAssertEqual(manifest.layers[0].digest, Self.layerDiffID)
        XCTAssertEqual(manifest.layers[0].size, 1000)
        XCTAssertEqual(index.manifests[0].digest, OCIDigest.sha256(of: manifestData))
    }

    func testMismatchedDiffIDIsRejected() async throws {
        let bogus = "sha256:" + String(repeating: "c", count: 64)
        let (resolved, gzip) = try makeResolved(diffIDs: [bogus])

        do {
            _ = try await ImageMaterializer.materialize(
                resolved,
                into: root,
                decompressLayers: true,
                fetchBlob: { _ in gzip }
            )
            XCTFail("Expected a diff_id mismatch to abort the pull")
        } catch let error as ImageLayoutError {
            guard case .diffIDMismatch = error else {
                return XCTFail("Unexpected layout error: \(error)")
            }
        }
    }

    func testKeepsCompressedLayersWhenAsked() async throws {
        let (resolved, gzip) = try makeResolved(diffIDs: [Self.layerDiffID])

        let result = try await ImageMaterializer.materialize(
            resolved,
            into: root,
            decompressLayers: false,
            fetchBlob: { _ in gzip }
        )

        XCTAssertEqual(result.decompressedLayerCount, 0)
        let layout = ImageLayout(root: root)
        let storedURL = try layout.blobURL(for: resolved.manifest.layers[0].digest)
        XCTAssertTrue(FileManager.default.fileExists(atPath: storedURL.path))
    }
}

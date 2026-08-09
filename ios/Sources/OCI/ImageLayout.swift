import Foundation

/// Writes an [OCI Image Layout](https://github.com/opencontainers/image-spec/blob/main/image-layout.md)
/// on disk: `oci-layout`, `index.json`, and content-addressed `blobs/sha256/…`.
///
/// This is the handoff format to the wasm runtime — container2wasm's
/// `imagemounter` consumes exactly this directory shape over HTTP.
struct ImageLayout {
    let root: URL

    static let layoutVersion = "1.0.0"
    static let refNameAnnotation = "org.opencontainers.image.ref.name"

    var blobsDirectory: URL {
        root.appendingPathComponent("blobs", isDirectory: true)
            .appendingPathComponent("sha256", isDirectory: true)
    }

    func blobURL(for digest: String) throws -> URL {
        guard let hex = OCIDigest.hex(digest) else {
            throw ImageLayoutError.invalidDigest(digest)
        }
        return blobsDirectory.appendingPathComponent(hex, isDirectory: false)
    }

    func prepare() throws {
        let fileManager = FileManager.default
        try fileManager.createDirectory(at: blobsDirectory, withIntermediateDirectories: true)
        let marker = ["imageLayoutVersion": Self.layoutVersion]
        let data = try JSONSerialization.data(withJSONObject: marker, options: [.sortedKeys])
        try data.write(to: root.appendingPathComponent("oci-layout"), options: .atomic)
    }

    /// Writes a blob under its digest. Existing blobs are left alone — content
    /// addressing means a matching name is already the right bytes.
    @discardableResult
    func writeBlob(_ data: Data, digest: String) throws -> URL {
        let url = try blobURL(for: digest)
        if FileManager.default.fileExists(atPath: url.path) {
            return url
        }
        try data.write(to: url, options: .atomic)
        return url
    }

    func writeIndex(manifest: OCIDescriptor, refName: String?) throws {
        var descriptor = manifest
        if let refName {
            var annotations = descriptor.annotations ?? [:]
            annotations[Self.refNameAnnotation] = refName
            descriptor.annotations = annotations
        }
        let index = OCIIndex(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociIndex,
            manifests: [descriptor]
        )
        let data = try ImageLayout.encoder.encode(index)
        try data.write(to: root.appendingPathComponent("index.json"), options: .atomic)
    }

    func readIndex() throws -> OCIIndex {
        let data = try Data(contentsOf: root.appendingPathComponent("index.json"))
        return try JSONDecoder().decode(OCIIndex.self, from: data)
    }

    /// Sorted keys keep the bytes (and therefore the manifest digest) stable
    /// across runs, which makes the layout reproducible and testable.
    static let encoder: JSONEncoder = {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.sortedKeys, .withoutEscapingSlashes]
        return encoder
    }()
}

enum ImageLayoutError: Error, LocalizedError {
    case invalidDigest(String)
    case diffIDMismatch(index: Int, expected: String, actual: String)

    var errorDescription: String? {
        switch self {
        case .invalidDigest(let digest):
            return "Not a usable digest: \(digest)"
        case .diffIDMismatch(let index, let expected, let actual):
            return "Layer \(index) decompressed to \(actual) but the image config says \(expected)"
        }
    }
}

/// The result of pulling an image all the way to disk.
struct MaterializedImage: Equatable {
    var root: URL
    var reference: String
    var manifestDigest: String
    var platform: OCIPlatform
    var layerCount: Int
    var decompressedLayerCount: Int
    var bytesOnDisk: Int64
    var commandLine: [String]
}

/// Pulls every blob of a resolved image into an on-disk OCI layout.
///
/// When `decompressLayers` is on, gzip layers are inflated natively and the
/// manifest is rewritten to reference the uncompressed tars. That is safe and
/// self-checking: the digest of an uncompressed layer is by definition the
/// `diff_id` already recorded in the image config, so a mismatch means
/// something went wrong and we stop.
enum ImageMaterializer {
    static func materialize(
        _ resolved: ResolvedImage,
        into root: URL,
        decompressLayers: Bool,
        fetchBlob: (OCIDescriptor) async throws -> Data,
        progress: ((Int, Int) async -> Void)? = nil
    ) async throws -> MaterializedImage {
        let layout = ImageLayout(root: root)
        try layout.prepare()

        try layout.writeBlob(resolved.configData, digest: resolved.manifest.config.digest)

        let diffIDs = resolved.config.rootfs?.diffIDs ?? []
        var layerDescriptors: [OCIDescriptor] = []
        var decompressedCount = 0
        let total = resolved.manifest.layers.count

        for (index, layer) in resolved.manifest.layers.enumerated() {
            await progress?(index, total)
            let blob = try await fetchBlob(layer)

            if decompressLayers, OCIMediaType.isGzipLayer(layer.mediaType), Gunzip.isGzip(blob) {
                let inflated = try Gunzip.decompress(blob)
                let digest = OCIDigest.sha256(of: inflated)
                if index < diffIDs.count, diffIDs[index] != digest {
                    throw ImageLayoutError.diffIDMismatch(
                        index: index,
                        expected: diffIDs[index],
                        actual: digest
                    )
                }
                try layout.writeBlob(inflated, digest: digest)
                layerDescriptors.append(
                    OCIDescriptor(
                        mediaType: OCIMediaType.ociLayerTar,
                        digest: digest,
                        size: Int64(inflated.count),
                        platform: nil,
                        annotations: layer.annotations
                    )
                )
                decompressedCount += 1
            } else {
                try layout.writeBlob(blob, digest: layer.digest)
                layerDescriptors.append(layer)
            }
        }
        await progress?(total, total)

        let manifest = OCIManifest(
            schemaVersion: 2,
            mediaType: OCIMediaType.ociManifest,
            config: OCIDescriptor(
                mediaType: OCIMediaType.ociConfig,
                digest: resolved.manifest.config.digest,
                size: Int64(resolved.configData.count),
                platform: nil,
                annotations: nil
            ),
            layers: layerDescriptors,
            annotations: nil
        )
        let manifestData = try ImageLayout.encoder.encode(manifest)
        let manifestDigest = OCIDigest.sha256(of: manifestData)
        try layout.writeBlob(manifestData, digest: manifestDigest)

        let manifestDescriptor = OCIDescriptor(
            mediaType: OCIMediaType.ociManifest,
            digest: manifestDigest,
            size: Int64(manifestData.count),
            platform: resolved.platform,
            annotations: nil
        )
        try layout.writeIndex(manifest: manifestDescriptor, refName: resolved.reference.canonicalName)

        return MaterializedImage(
            root: root,
            reference: resolved.reference.canonicalName,
            manifestDigest: manifestDigest,
            platform: resolved.platform,
            layerCount: layerDescriptors.count,
            decompressedLayerCount: decompressedCount,
            bytesOnDisk: directorySize(root),
            commandLine: resolved.config.commandLine
        )
    }

    static func directorySize(_ url: URL) -> Int64 {
        guard let enumerator = FileManager.default.enumerator(
            at: url,
            includingPropertiesForKeys: [.fileSizeKey],
            options: [.skipsHiddenFiles]
        ) else { return 0 }

        var total: Int64 = 0
        for case let fileURL as URL in enumerator {
            let size = (try? fileURL.resourceValues(forKeys: [.fileSizeKey]))?.fileSize ?? 0
            total += Int64(size)
        }
        return total
    }
}

import Foundation
import SwiftUI

enum TargetArchitecture: String, CaseIterable, Identifiable {
    case arm64
    case amd64

    var id: String { rawValue }

    var platform: OCIPlatform {
        switch self {
        case .arm64: return .linuxArm64
        case .amd64: return .linuxAmd64
        }
    }

    var label: String { "linux/\(rawValue)" }
}

/// Drives the Container Lab experiment: resolve a reference, pull it to an OCI
/// layout on disk, and report whether the webview runtime environment is
/// capable of running it.
@MainActor
final class ContainerLabModel: ObservableObject {
    @Published var imageText: String = "alpine:3.20"
    @Published var architecture: TargetArchitecture = .arm64
    @Published var isBusy = false
    @Published var statusMessage = "Ready"
    @Published var errorMessage: String?
    @Published private(set) var resolved: ResolvedImage?
    @Published private(set) var materialized: MaterializedImage?
    @Published private(set) var isolation: CrossOriginIsolationProbe.Result?
    @Published private(set) var isolationMessage = "Not checked yet"

    private let client = RegistryClient()
    private let runtimeServer = ContainerRuntimeServer()

    var runtimeStatus: String { RuntimeAssets.status }
    var isRuntimeInstalled: Bool { RuntimeAssets.isInstalled }

    var layerRows: [LayerRow] {
        guard let resolved else { return [] }
        return resolved.manifest.layers.enumerated().map { index, layer in
            LayerRow(
                index: index,
                digest: layer.digest,
                size: layer.size,
                mediaType: layer.mediaType
            )
        }
    }

    struct LayerRow: Identifiable {
        let index: Int
        let digest: String
        let size: Int64
        let mediaType: String

        var id: String { "\(index)-\(digest)" }

        var shortDigest: String {
            guard let hex = OCIDigest.hex(digest) else { return digest }
            return String(hex.prefix(12))
        }

        var isCompressed: Bool { OCIMediaType.isGzipLayer(mediaType) }
    }

    // MARK: - Actions

    func inspect() async {
        guard !isBusy else { return }
        isBusy = true
        errorMessage = nil
        materialized = nil
        defer { isBusy = false }

        do {
            let reference = try ImageReference(parsing: imageText)
            statusMessage = "Resolving \(reference.canonicalName)…"
            let image = try await client.resolve(reference, platform: architecture.platform)
            resolved = image
            statusMessage = "Resolved \(image.platform.displayName) · "
                + "\(image.manifest.layers.count) layer\(image.manifest.layers.count == 1 ? "" : "s") · "
                + Self.byteFormatter.string(fromByteCount: image.totalLayerSize)
        } catch {
            resolved = nil
            statusMessage = "Resolve failed"
            errorMessage = Self.describe(error)
        }
    }

    func materialize() async {
        guard !isBusy, let image = resolved else { return }
        isBusy = true
        errorMessage = nil
        defer { isBusy = false }

        do {
            let root = try Self.storageRoot(for: image.reference)
            statusMessage = "Pulling layers…"
            let result = try await ImageMaterializer.materialize(
                image,
                into: root,
                decompressLayers: true,
                fetchBlob: { [client] descriptor in
                    try await client.fetchBlob(descriptor, from: image.reference)
                },
                progress: { [weak self] done, total in
                    await MainActor.run {
                        self?.statusMessage = "Pulling layer \(min(done + 1, total)) of \(total)…"
                    }
                }
            )
            materialized = result
            runtimeServer.update(imageRoot: result.root)
            statusMessage = "Image layout ready · "
                + Self.byteFormatter.string(fromByteCount: result.bytesOnDisk)
                + " on disk · \(result.decompressedLayerCount) layer(s) decompressed natively"
        } catch {
            statusMessage = "Pull failed"
            errorMessage = Self.describe(error)
        }
    }

    /// The kill-switch check from the design doc: without cross-origin
    /// isolation in a `WKWebView` there is no wasm-threaded emulator.
    func checkIsolation() async {
        guard !isBusy else { return }
        isBusy = true
        defer { isBusy = false }

        isolationMessage = "Starting loopback server…"
        do {
            _ = try await runtimeServer.start(imageRoot: materialized?.root)
            guard let probeURL = runtimeServer.probeURL else {
                throw LoopbackServerError.noPort
            }
            isolationMessage = "Loading \(probeURL.absoluteString)…"
            let probe = CrossOriginIsolationProbe()
            let result = try await probe.run(url: probeURL)
            isolation = result
            isolationMessage = result.summary
        } catch {
            isolation = nil
            isolationMessage = "Check failed: \(Self.describe(error))"
        }
    }

    // MARK: - Helpers

    static func storageRoot(for reference: ImageReference) throws -> URL {
        let caches = try FileManager.default.url(
            for: .cachesDirectory,
            in: .userDomainMask,
            appropriateFor: nil,
            create: true
        )
        let slug = reference.canonicalName
            .replacingOccurrences(of: "/", with: "_")
            .replacingOccurrences(of: ":", with: "_")
            .replacingOccurrences(of: "@", with: "_")
        return caches
            .appendingPathComponent("ContainerLab", isDirectory: true)
            .appendingPathComponent(slug, isDirectory: true)
    }

    static let byteFormatter: ByteCountFormatter = {
        let formatter = ByteCountFormatter()
        formatter.countStyle = .file
        return formatter
    }()

    static func describe(_ error: Error) -> String {
        if let localized = error as? LocalizedError, let description = localized.errorDescription {
            return description
        }
        return error.localizedDescription
    }
}

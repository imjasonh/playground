import Foundation

/// Media types we ask for and recognize. Docker (schema 2) and OCI types are
/// both accepted — Docker Hub still serves the Docker types by default.
enum OCIMediaType {
    static let ociIndex = "application/vnd.oci.image.index.v1+json"
    static let ociManifest = "application/vnd.oci.image.manifest.v1+json"
    static let ociConfig = "application/vnd.oci.image.config.v1+json"
    static let ociLayerGzip = "application/vnd.oci.image.layer.v1.tar+gzip"
    static let ociLayerTar = "application/vnd.oci.image.layer.v1.tar"
    static let ociLayerZstd = "application/vnd.oci.image.layer.v1.tar+zstd"

    static let dockerManifestList = "application/vnd.docker.distribution.manifest.list.v2+json"
    static let dockerManifest = "application/vnd.docker.distribution.manifest.v2+json"
    static let dockerConfig = "application/vnd.docker.container.image.v1+json"
    static let dockerLayerGzip = "application/vnd.docker.image.rootfs.diff.tar.gzip"

    /// Sent as the `Accept` header when resolving a reference.
    static let manifestAccept = [
        ociIndex, ociManifest, dockerManifestList, dockerManifest
    ].joined(separator: ", ")

    static func isIndex(_ mediaType: String?) -> Bool {
        mediaType == ociIndex || mediaType == dockerManifestList
    }

    static func isManifest(_ mediaType: String?) -> Bool {
        mediaType == ociManifest || mediaType == dockerManifest
    }

    static func isGzipLayer(_ mediaType: String) -> Bool {
        mediaType == ociLayerGzip || mediaType == dockerLayerGzip
    }
}

struct OCIPlatform: Codable, Equatable {
    var architecture: String
    var os: String
    var variant: String?

    /// The platform an iOS device would run natively, and our default target.
    static let linuxArm64 = OCIPlatform(architecture: "arm64", os: "linux", variant: nil)
    static let linuxAmd64 = OCIPlatform(architecture: "amd64", os: "linux", variant: nil)

    var displayName: String {
        if let variant, !variant.isEmpty {
            return "\(os)/\(architecture)/\(variant)"
        }
        return "\(os)/\(architecture)"
    }
}

struct OCIDescriptor: Codable, Equatable {
    var mediaType: String
    var digest: String
    var size: Int64
    var platform: OCIPlatform?
    var annotations: [String: String]?
}

struct OCIIndex: Codable, Equatable {
    var schemaVersion: Int?
    var mediaType: String?
    var manifests: [OCIDescriptor]
}

struct OCIManifest: Codable, Equatable {
    var schemaVersion: Int?
    var mediaType: String?
    /// Set by artifacts, absent on images. It is how a registry tells you the
    /// manifest describes something that is not a container root filesystem.
    var artifactType: String?
    var config: OCIDescriptor
    var layers: [OCIDescriptor]
    var annotations: [String: String]?
}

/// The subset of the image config we surface. Docker and OCI both capitalize
/// the keys inside `config`.
struct OCIImageConfig: Codable, Equatable {
    struct RunConfig: Codable, Equatable {
        var entrypoint: [String]?
        var cmd: [String]?
        var env: [String]?
        var workingDir: String?
        var user: String?

        enum CodingKeys: String, CodingKey {
            case entrypoint = "Entrypoint"
            case cmd = "Cmd"
            case env = "Env"
            case workingDir = "WorkingDir"
            case user = "User"
        }
    }

    struct RootFS: Codable, Equatable {
        var type: String?
        var diffIDs: [String]?

        enum CodingKeys: String, CodingKey {
            case type
            case diffIDs = "diff_ids"
        }
    }

    var architecture: String?
    var os: String?
    var variant: String?
    var config: RunConfig?
    var rootfs: RootFS?

    /// What the runtime would execute: entrypoint followed by cmd.
    var commandLine: [String] {
        (config?.entrypoint ?? []) + (config?.cmd ?? [])
    }
}

/// A reference resolved down to one concrete manifest for one platform.
struct ResolvedImage: Equatable {
    var reference: ImageReference
    var manifestDescriptor: OCIDescriptor
    var manifestData: Data
    var manifest: OCIManifest
    var configData: Data
    var config: OCIImageConfig

    var totalLayerSize: Int64 {
        manifest.layers.reduce(0) { $0 + $1.size }
    }

    var platform: OCIPlatform {
        OCIPlatform(
            architecture: config.architecture ?? manifestDescriptor.platform?.architecture ?? "unknown",
            os: config.os ?? manifestDescriptor.platform?.os ?? "unknown",
            variant: config.variant ?? manifestDescriptor.platform?.variant
        )
    }
}

/// Picks one manifest out of an index for the platform we want.
///
/// Pure and separately tested: an exact `os`/`architecture`/`variant` match
/// wins, then a match ignoring variant, and attestation entries (which carry
/// `unknown/unknown`) are always skipped.
enum PlatformMatcher {
    static func select(from index: OCIIndex, matching wanted: OCIPlatform) -> OCIDescriptor? {
        let candidates = index.manifests.filter { descriptor in
            guard let platform = descriptor.platform else { return false }
            return platform.os != "unknown" && platform.architecture != "unknown"
        }

        if let exact = candidates.first(where: { descriptor in
            guard let platform = descriptor.platform else { return false }
            return platform.os == wanted.os
                && platform.architecture == wanted.architecture
                && normalizedVariant(platform, architecture: platform.architecture)
                    == normalizedVariant(wanted, architecture: wanted.architecture)
        }) {
            return exact
        }

        return candidates.first { descriptor in
            guard let platform = descriptor.platform else { return false }
            return platform.os == wanted.os && platform.architecture == wanted.architecture
        }
    }

    /// `arm64` and `arm64/v8` name the same thing; treat the default variant as absent.
    private static func normalizedVariant(_ platform: OCIPlatform, architecture: String) -> String {
        let variant = platform.variant ?? ""
        if architecture == "arm64" && variant == "v8" { return "" }
        if architecture == "amd64" && variant == "v1" { return "" }
        return variant
    }
}

import Foundation

/// Finds the WebAssembly module inside an OCI artifact.
///
/// This is not a container image. There is no root filesystem to assemble and
/// nothing to `exec`; the manifest carries one blob that happens to be a wasm
/// module, and OCI is only how it travelled. So instead of Container Lab's
/// layer-stacking, all that is needed here is picking the right descriptor.
///
/// Nobody has standardized the media types, so this recognizes the ones in
/// circulation and then falls back on weaker evidence rather than refusing a
/// perfectly good module over a spelling difference.
enum WasmArtifact {
    /// Layer types seen from `oras`, `docker buildx --platform wasi/wasm`, and
    /// the wasmCloud/Spin tooling.
    static let layerMediaTypes: Set<String> = [
        "application/wasm",
        "application/vnd.wasm.content.layer.v1+wasm",
        "application/vnd.module.wasm.content.layer.v1+wasm",
        "application/vnd.oci.image.layer.v1.wasm",
    ]

    /// Config / artifact types that mark the whole manifest as carrying wasm.
    static let artifactTypes: Set<String> = [
        "application/vnd.wasm.config.v0+json",
        "application/vnd.wasm.config.v1+json",
        "application/vnd.module.wasm.config.v1+json",
        "application/vnd.wasm.component.v0",
    ]

    enum SelectionError: Error, LocalizedError {
        case noLayers
        case notWasm(layerTypes: [String])

        var errorDescription: String? {
            switch self {
            case .noLayers:
                return "This reference has no layers, so there is no module to run"
            case .notWasm(let layerTypes):
                let listed = layerTypes.isEmpty ? "none" : layerTypes.joined(separator: ", ")
                return "No WebAssembly layer here (found: \(listed)). "
                    + "Wasm Service runs a wasm module pushed as an OCI artifact, not a container image."
            }
        }
    }

    /// The descriptor to pull, or an error explaining what was found instead.
    static func moduleLayer(in manifest: OCIManifest) throws -> OCIDescriptor {
        guard !manifest.layers.isEmpty else { throw SelectionError.noLayers }

        if let byMediaType = manifest.layers.first(where: { isWasmMediaType($0.mediaType) }) {
            return byMediaType
        }

        // A manifest that declares itself wasm and carries exactly one blob is
        // unambiguous even when whoever pushed it labelled the layer as opaque
        // bytes, which `oras push` does by default.
        if manifest.layers.count == 1, isWasmArtifactType(manifest.artifactType)
            || isWasmArtifactType(manifest.config.mediaType) {
            return manifest.layers[0]
        }

        if let byName = manifest.layers.first(where: { descriptor in
            (descriptor.annotations?["org.opencontainers.image.title"] ?? "").hasSuffix(".wasm")
        }) {
            return byName
        }

        throw SelectionError.notWasm(layerTypes: manifest.layers.map(\.mediaType))
    }

    static func isWasmMediaType(_ mediaType: String) -> Bool {
        layerMediaTypes.contains(mediaType) || mediaType.hasSuffix("+wasm")
    }

    static func isWasmArtifactType(_ type: String?) -> Bool {
        guard let type, !type.isEmpty else { return false }
        return artifactTypes.contains(type) || type.contains("wasm")
    }
}

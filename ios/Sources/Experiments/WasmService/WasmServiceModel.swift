import Foundation
import SwiftUI

/// Drives the Wasm Service experiment: pull a WebAssembly module from a
/// registry, run it inside the app, and serve it over a real TCP port.
///
/// A singleton, unlike the other experiments' models, because the service has
/// to outlive its view. The whole point is a server that keeps running — if
/// navigating back to the launcher tore it down, "long running" would mean
/// "for as long as you stare at it".
@MainActor
final class WasmServiceModel: ObservableObject {
    static let shared = WasmServiceModel()

    enum Phase: Equatable {
        case idle
        case pulling
        case starting
        case serving(port: UInt16)
        case failed(String)

        var isBusy: Bool {
            switch self {
            case .pulling, .starting: return true
            case .idle, .serving, .failed: return false
            }
        }
    }

    /// The demo payload, built and published by this repo's `wasm-hello` app.
    static let defaultReference = "ghcr.io/imjasonh/playground/wasm-hello:latest"

    @Published var referenceText = WasmServiceModel.defaultReference
    @Published var portText = "8080"
    /// Off means loopback only — reachable from Safari on this device and
    /// nothing else.
    @Published var reachableOnNetwork = true

    @Published private(set) var phase: Phase = .idle
    @Published private(set) var statusMessage = "Nothing loaded"
    @Published private(set) var errorMessage: String?
    @Published private(set) var log: [String] = []
    @Published private(set) var summary: WasmHTTPGuest.Summary?
    @Published private(set) var requestsServed = 0
    @Published private(set) var addresses: [LocalAddresses.Interface] = []
    @Published private(set) var loadedModule: LoadedModule?

    struct LoadedModule: Equatable {
        var reference: String
        var digest: String
        var byteCount: Int
        var mediaType: String
        var cameFromCache: Bool
    }

    let background = WasmServiceBackground.shared

    private let client = RegistryClient()
    private let store = WasmModuleStore.shared
    private let runtime = WasmServiceRuntime()
    /// The log is for watching a service, not archiving it.
    private static let logLimit = 300

    private init() {
        runtime.onLog = { [weak self] line in
            Task { @MainActor in self?.append(line) }
        }
        runtime.onRequestServed = { [weak self] total in
            Task { @MainActor in self?.requestsServed = total }
        }
        background.resumeService = { [weak self] in
            await self?.startFromCache() ?? false
        }
        if let record = store.lastRecord {
            referenceText = record.reference
            portText = String(record.port)
        }
    }

    var isServing: Bool {
        if case .serving = phase { return true }
        return false
    }

    /// The URLs worth showing, most useful first.
    var serviceURLs: [String] {
        guard case .serving(let port) = phase else { return [] }
        return addresses.map { "http://\($0.address):\(port)/" }
    }

    // MARK: - Actions

    func pullAndStart() async {
        guard !phase.isBusy else { return }
        errorMessage = nil
        phase = .pulling
        statusMessage = "Resolving \(referenceText)…"

        do {
            let reference = try ImageReference(parsing: referenceText)
            let resolved = try await client.resolve(reference, platform: Self.wasmPlatform)
            let descriptor = try WasmArtifact.moduleLayer(in: resolved.manifest)

            statusMessage = "Pulling \(Self.humanSize(descriptor.size))…"
            // The client verifies the blob against this digest before it
            // returns, so a module that reaches here is the one the manifest
            // named.
            let module = try await client.fetchBlob(descriptor, from: reference)
            try store.save(module, digest: descriptor.digest)

            loadedModule = LoadedModule(
                reference: referenceText,
                digest: descriptor.digest,
                byteCount: module.count,
                mediaType: descriptor.mediaType,
                cameFromCache: false
            )
            append("Pulled \(descriptor.digest.prefix(19))… (\(Self.humanSize(Int64(module.count))))")
            await start(module: module, digest: descriptor.digest)
        } catch {
            fail(error)
        }
    }

    /// Brings the last-used module back up without touching the network.
    /// The background window calls this, so it must not need a UI or a pull.
    @discardableResult
    func startFromCache() async -> Bool {
        if isServing { return true }
        guard let record = store.lastRecord, let module = store.load(digest: record.digest) else {
            return false
        }
        referenceText = record.reference
        portText = String(record.port)
        loadedModule = LoadedModule(
            reference: record.reference,
            digest: record.digest,
            byteCount: module.count,
            mediaType: "application/wasm",
            cameFromCache: true
        )
        await start(module: module, digest: record.digest)
        return isServing
    }

    func stop() {
        runtime.stop()
        phase = .idle
        statusMessage = "Stopped"
        addresses = []
        append("Service stopped")
    }

    func refreshAddresses() {
        guard isServing else { return }
        addresses = LocalAddresses.current()
    }

    // MARK: - Lifecycle hooks from the view

    func applicationWillResignActive() {
        guard isServing else { return }
        background.beginShortAssertion()
        background.scheduleNextWindow()
    }

    func applicationDidBecomeActive() {
        background.endShortAssertion()
        refreshAddresses()
    }

    // MARK: - Internals

    private func start(module: Data, digest: String) async {
        phase = .starting
        statusMessage = "Starting the module…"

        let port = UInt16(portText) ?? 8080
        do {
            let started = try await runtime.start(
                module: module,
                configuration: WasmServiceRuntime.Configuration(
                    port: port,
                    loopbackOnly: !reachableOnNetwork
                )
            )
            summary = started.summary
            requestsServed = 0
            phase = .serving(port: started.port)
            portText = String(started.port)
            addresses = LocalAddresses.current()
            statusMessage = "Serving on port \(started.port)"
            store.lastRecord = WasmModuleStore.Record(
                reference: referenceText, digest: digest, port: started.port
            )
            append("Serving on port \(started.port) — ABI v\(started.summary.abiVersion)")
            if background.keepAliveEnabled {
                background.scheduleNextWindow()
            }
        } catch {
            runtime.stop()
            fail(error)
        }
    }

    private func fail(_ error: Error) {
        let message = error.localizedDescription
        phase = .failed(message)
        statusMessage = "Failed"
        errorMessage = message
        append("Error: \(message)")
    }

    private func append(_ line: String) {
        log.append(line)
        if log.count > Self.logLimit {
            log.removeFirst(log.count - Self.logLimit)
        }
    }

    /// What a wasm artifact's index entry looks like when it has one. Most are
    /// single manifests with no platform at all, in which case this is unused.
    static let wasmPlatform = OCIPlatform(architecture: "wasm", os: "wasip1", variant: nil)

    static func humanSize(_ bytes: Int64) -> String {
        let formatter = ByteCountFormatter()
        formatter.countStyle = .binary
        return formatter.string(fromByteCount: bytes)
    }
}

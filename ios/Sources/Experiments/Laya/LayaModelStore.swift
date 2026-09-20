import CoreML
import Foundation
import Hub

/// Where the model comes from. Pinned to the 0.1.0 release revision so a Hub
/// push cannot change what the app runs.
enum LayaModelSource {
    static let repoID = "aac6fef/laya-multilingual-coreml-ane"
    static let revision = "39d6a9b3d0f67f06da74fbade6121ea134cbdb21"
    /// `bundle_bytes` from the release inventory.
    static let approximateBytes: Int64 = 679_920_639
    static let hubURL = URL(string: "https://huggingface.co/\(repoID)") ?? URL(fileURLWithPath: "/")
    static let sourceURL = URL(string: "https://github.com/mizorewww/laya-coreml") ?? URL(fileURLWithPath: "/")

    static var shortRevision: String { String(revision.prefix(7)) }
}

/// Lifecycle of the on-device bundle.
enum LayaModelPhase: Equatable {
    case notDownloaded
    case downloading(fraction: Double)
    case verifying
    case compiling
    case loading
    case ready
    case failed(String)

    var isBusy: Bool {
        switch self {
        case .downloading, .verifying, .compiling, .loading: return true
        case .notDownloaded, .ready, .failed: return false
        }
    }
}

/// Downloads, verifies, compiles, and loads the ANE bundle; then answers questions.
@MainActor
final class LayaModelStore: ObservableObject {
    @Published private(set) var phase: LayaModelPhase = .notDownloaded
    @Published private(set) var info: LayaModelInfo?
    @Published private(set) var isPredicting = false

    private var runtime: LayaRuntime?
    private let baseDirectory: URL
    private let computeUnits: MLComputeUnits

    static var isSimulator: Bool {
        #if targetEnvironment(simulator)
        return true
        #else
        return false
        #endif
    }

    init(baseDirectory: URL? = nil, computeUnits: MLComputeUnits = .cpuAndNeuralEngine) {
        let base = baseDirectory ?? FileManager.default
            .urls(for: .applicationSupportDirectory, in: .userDomainMask)[0]
            .appendingPathComponent("Laya", isDirectory: true)
        self.baseDirectory = base
        self.computeUnits = computeUnits
    }

    var isDownloaded: Bool {
        FileManager.default.fileExists(atPath: Self.verifiedMarker(baseDirectory).path)
    }

    var maxTokens: Int? { runtime?.maxTokens }

    // MARK: Paths

    private static func hubBase(_ base: URL) -> URL {
        base.appendingPathComponent("hub", isDirectory: true)
    }

    private static func bundleRoot(_ base: URL) -> URL {
        HubApi(downloadBase: hubBase(base), cache: nil).localRepoLocation(Hub.Repo(id: LayaModelSource.repoID))
    }

    private static func verifiedMarker(_ base: URL) -> URL {
        bundleRoot(base).appendingPathComponent(".laya-verified")
    }

    private static func compiledModel(_ base: URL) -> URL {
        base
            .appendingPathComponent("compiled", isDirectory: true)
            .appendingPathComponent(LayaModelSource.revision, isDirectory: true)
            .appendingPathComponent("model.mlmodelc", isDirectory: true)
    }

    // MARK: Lifecycle

    /// Downloads if needed, then compiles and loads. Safe to call again after a failure.
    func prepare() async {
        guard !phase.isBusy, runtime == nil else { return }
        do {
            let root = Self.bundleRoot(baseDirectory)
            if !isDownloaded {
                try await download(to: root)
            }
            let bundle = try LayaBundle(root: root)
            let compiled = try await compileIfNeeded(package: bundle.packageURL)
            phase = .loading
            let units = computeUnits
            let revision = LayaModelSource.shortRevision
            let loaded = try await Task.detached(priority: .userInitiated) {
                try await LayaRuntime(bundle: bundle, compiledModelURL: compiled, revision: revision, computeUnits: units)
            }.value
            runtime = loaded
            info = loaded.info
            phase = .ready
        } catch {
            phase = .failed(Self.describe(error))
        }
    }

    private func download(to root: URL) async throws {
        phase = .downloading(fraction: 0)
        let hub = HubApi(downloadBase: Self.hubBase(baseDirectory), cache: nil)
        try await hub.snapshot(
            from: Hub.Repo(id: LayaModelSource.repoID),
            revision: LayaModelSource.revision,
            matching: LayaBundleFile.downloadGlobs
        ) { progress in
            let fraction = progress.fractionCompleted
            Task { @MainActor [weak self] in
                guard let self, case .downloading = self.phase else { return }
                self.phase = .downloading(fraction: fraction)
            }
        }
        phase = .verifying
        let bundle = try LayaBundle(root: root)
        try await Task.detached(priority: .userInitiated) {
            try bundle.verifyFiles()
        }.value
        try LayaModelSource.revision.write(to: Self.verifiedMarker(baseDirectory), atomically: true, encoding: .utf8)
    }

    private func compileIfNeeded(package: URL) async throws -> URL {
        let destination = Self.compiledModel(baseDirectory)
        if FileManager.default.fileExists(atPath: destination.path) {
            return destination
        }
        phase = .compiling
        let temporary = try await MLModel.compileModel(at: package)
        try FileManager.default.createDirectory(
            at: destination.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        try FileManager.default.moveItem(at: temporary, to: destination)
        return destination
    }

    /// Removes the download and the compiled graph.
    func deleteModel() {
        guard !phase.isBusy else { return }
        runtime = nil
        info = nil
        try? FileManager.default.removeItem(at: baseDirectory)
        phase = .notDownloaded
    }

    // MARK: Inference

    func predict(state: String, question: LayaQuestion) async throws -> LayaPrediction {
        guard let runtime else {
            throw LayaError.model("The model is not loaded.")
        }
        isPredicting = true
        defer { isPredicting = false }
        return try await Task.detached(priority: .userInitiated) {
            try runtime.predict(state: state, question: question)
        }.value
    }

    /// Prepared-sequence token count, or nil when the runtime is not loaded.
    func tokenCount(state: String, question: LayaQuestion) -> Result<Int, Error>? {
        guard let runtime else { return nil }
        return Result { try runtime.tokenCount(state: state, question: question) }
    }

    private static func describe(_ error: Error) -> String {
        if let laya = error as? LayaError {
            return laya.errorDescription ?? "Unknown error"
        }
        let text = error.localizedDescription
        if (error as NSError).domain == NSURLErrorDomain {
            return "Download failed: \(text)"
        }
        return text
    }
}

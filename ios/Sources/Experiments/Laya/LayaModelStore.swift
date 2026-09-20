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
    case failed(LayaFailure)

    var isBusy: Bool {
        switch self {
        case .downloading, .verifying, .compiling, .loading: return true
        case .notDownloaded, .ready, .failed: return false
        }
    }

    var failure: LayaFailure? {
        if case .failed(let failure) = self { return failure }
        return nil
    }
}

/// The compute-unit choices the UI offers, persisted by raw value.
enum LayaComputeChoice: Int, CaseIterable, Identifiable {
    case cpuAndNeuralEngine
    case all
    case cpuAndGPU
    case cpuOnly

    var id: Int { rawValue }

    var units: MLComputeUnits {
        switch self {
        case .cpuAndNeuralEngine: return .cpuAndNeuralEngine
        case .all: return .all
        case .cpuAndGPU: return .cpuAndGPU
        case .cpuOnly: return .cpuOnly
        }
    }

    var title: String { LayaRuntime.label(for: units) }
}

/// Downloads, verifies, compiles, and loads the ANE bundle; then answers
/// questions. Every stage is timed and logged so a TestFlight run can be
/// debugged from the copied report.
@MainActor
final class LayaModelStore: ObservableObject {
    @Published private(set) var phase: LayaModelPhase = .notDownloaded
    @Published private(set) var info: LayaModelInfo?
    @Published private(set) var isPredicting = false
    @Published private(set) var stages: [LayaStageTiming] = []
    @Published private(set) var log = LayaLogBuffer()
    @Published private(set) var history: [LayaPrediction] = []
    @Published private(set) var benchmark: LayaBenchmarkReport?
    @Published private(set) var isBenchmarking = false
    @Published private(set) var computePlan: LayaComputePlanSummary?
    @Published private(set) var isPlanning = false
    @Published private(set) var device = LayaDeviceStats.report()
    /// Resident memory before and after the runtime was built.
    @Published private(set) var loadMemory: (before: Int64, after: Int64)?
    @Published var computeChoice: LayaComputeChoice {
        didSet {
            guard computeChoice != oldValue else { return }
            UserDefaults.standard.set(computeChoice.rawValue, forKey: Self.computeChoiceKey)
            append("compute units → \(computeChoice.title)")
            if runtime != nil {
                unload()
            }
        }
    }

    private var runtime: LayaRuntime?
    private var compiledURL: URL?
    /// Last download decile written to the log.
    private var lastLoggedTenth = -1
    private let baseDirectory: URL
    private let logURL: URL
    static let computeChoiceKey = "layaComputeChoice"
    static let historyLimit = 25

    static var isSimulator: Bool { LayaDeviceStats.isSimulator }

    init(baseDirectory: URL? = nil) {
        let base = baseDirectory ?? FileManager.default
            .urls(for: .applicationSupportDirectory, in: .userDomainMask)[0]
            .appendingPathComponent("Laya", isDirectory: true)
        self.baseDirectory = base
        // Beside the model directory so **Delete download** keeps the history.
        self.logURL = base.deletingLastPathComponent().appendingPathComponent("Laya-diagnostics.log")
        let stored = UserDefaults.standard.object(forKey: Self.computeChoiceKey) as? Int
        self.computeChoice = stored.flatMap(LayaComputeChoice.init(rawValue:)) ?? .cpuAndNeuralEngine
        if let text = try? String(contentsOf: logURL, encoding: .utf8) {
            log.restore(from: text)
        }
        append("opened; downloaded=\(isDownloaded) compiled=\(FileManager.default.fileExists(atPath: Self.compiledModel(base).path)) \(computeChoice.title)")
    }

    var isDownloaded: Bool {
        FileManager.default.fileExists(atPath: Self.verifiedMarker(baseDirectory).path)
    }

    var maxTokens: Int? { runtime?.maxTokens }

    var lastPrediction: LayaPrediction? { history.last }

    /// Steady-state graph latency over the recent history.
    var graphStats: LayaLatencyStats? { LayaLatencyStats(history.map(\.timings.graph)) }
    var totalStats: LayaLatencyStats? { LayaLatencyStats(history.map(\.timings.total)) }

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

    // MARK: Logging

    private func append(_ message: String) {
        let entry = LayaLogEntry(date: Date(), message: message)
        log.append(entry.message, date: entry.date)
        let line = entry.line + "\n"
        if let data = line.data(using: .utf8) {
            if FileManager.default.fileExists(atPath: logURL.path),
               let handle = try? FileHandle(forWritingTo: logURL) {
                defer { try? handle.close() }
                _ = try? handle.seekToEnd()
                try? handle.write(contentsOf: data)
            } else {
                try? FileManager.default.createDirectory(at: logURL.deletingLastPathComponent(), withIntermediateDirectories: true)
                try? data.write(to: logURL)
            }
        }
    }

    private func record(_ stage: LayaStageTiming) {
        stages.removeAll { $0.name == stage.name }
        stages.append(stage)
        append("\(stage.name) took \(LayaFormat.seconds(stage.seconds))" + (stage.note.map { " (\($0))" } ?? ""))
    }

    private func fail(_ stage: String, _ error: Error) {
        let failure = LayaFailure(stage: stage, error: error)
        phase = .failed(failure)
        append("FAILED " + failure.report.replacingOccurrences(of: "\n", with: " | "))
    }

    func clearLog() {
        log = LayaLogBuffer()
        try? FileManager.default.removeItem(at: logURL)
        append("log cleared")
    }

    // MARK: Lifecycle

    /// Downloads if needed, then compiles and loads. Safe to call again after a failure.
    func prepare() async {
        guard !phase.isBusy, runtime == nil else { return }
        device = LayaDeviceStats.report()
        let root = Self.bundleRoot(baseDirectory)
        var stage = "download"
        do {
            if !isDownloaded {
                try await download(to: root)
            }
            stage = "read bundle"
            let bundle = try LayaBundle(root: root)
            append("bundle ok: shape \(bundle.manifest.shape.maxLength)×\(bundle.manifest.shape.maxOptions), hidden \(bundle.encoderConfig.hiddenSize), max_len \(bundle.agentConfig.maxLength)")
            stage = "compile"
            let compiled = try await compileIfNeeded(package: bundle.packageURL)
            compiledURL = compiled
            stage = "load"
            phase = .loading
            let before = LayaDeviceStats.residentMemoryBytes() ?? 0
            let units = computeChoice.units
            let revision = LayaModelSource.shortRevision
            let start = Date()
            let loaded = try await Task.detached(priority: .userInitiated) {
                try await LayaRuntime(bundle: bundle, compiledModelURL: compiled, revision: revision, computeUnits: units)
            }.value
            let after = LayaDeviceStats.residentMemoryBytes() ?? 0
            loadMemory = (before, after)
            runtime = loaded
            info = loaded.info
            record(LayaStageTiming(
                "load",
                seconds: Date().timeIntervalSince(start),
                note: "model \(LayaFormat.seconds(loaded.info.modelLoadSeconds)), tokenizer \(LayaFormat.seconds(loaded.info.tokenizerLoadSeconds)), weights \(LayaFormat.seconds(loaded.info.hostWeightsLoadSeconds)), +\(LayaFormat.bytes(after - before)) resident"
            ))
            append("signature: " + loaded.info.signature.text.replacingOccurrences(of: "\n", with: " | "))
            phase = .ready
        } catch {
            fail(stage, error)
        }
    }

    private func download(to root: URL) async throws {
        phase = .downloading(fraction: 0)
        let start = Date()
        append("download start \(LayaModelSource.repoID)@\(LayaModelSource.shortRevision) → \(root.path)")
        let hub = HubApi(downloadBase: Self.hubBase(baseDirectory), cache: nil)
        lastLoggedTenth = -1
        try await hub.snapshot(
            from: Hub.Repo(id: LayaModelSource.repoID),
            revision: LayaModelSource.revision,
            matching: LayaBundleFile.downloadGlobs
        ) { [weak self] progress in
            let fraction = progress.fractionCompleted
            let completed = progress.completedUnitCount
            let total = progress.totalUnitCount
            Task { @MainActor in
                guard let self, case .downloading = self.phase else { return }
                self.phase = .downloading(fraction: fraction)
                let tenth = Int(fraction * 10)
                if tenth > self.lastLoggedTenth {
                    self.lastLoggedTenth = tenth
                    self.append("download \(Int(fraction * 100))% (\(completed)/\(total) units, \(LayaFormat.seconds(Date().timeIntervalSince(start))))")
                }
            }
        }
        let downloadSeconds = Date().timeIntervalSince(start)
        let bytes = Self.directorySize(root)
        record(LayaStageTiming(
            "download",
            seconds: downloadSeconds,
            note: "\(LayaFormat.bytes(bytes)) at \(LayaFormat.throughput(bytes: bytes, seconds: downloadSeconds))"
        ))
        append("files: " + Self.fileListing(root))

        phase = .verifying
        let verifyStart = Date()
        let bundle = try LayaBundle(root: root)
        try await Task.detached(priority: .userInitiated) {
            try bundle.verifyFiles()
        }.value
        record(LayaStageTiming("verify", seconds: Date().timeIntervalSince(verifyStart), note: "\(bundle.manifest.files?.count ?? 0) manifest entries"))
        try LayaModelSource.revision.write(to: Self.verifiedMarker(baseDirectory), atomically: true, encoding: .utf8)
    }

    private func compileIfNeeded(package: URL) async throws -> URL {
        let destination = Self.compiledModel(baseDirectory)
        if FileManager.default.fileExists(atPath: destination.path) {
            append("compiled model cached at \(destination.lastPathComponent) (\(LayaFormat.bytes(Self.directorySize(destination))))")
            return destination
        }
        phase = .compiling
        let start = Date()
        let temporary = try await MLModel.compileModel(at: package)
        try FileManager.default.createDirectory(
            at: destination.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        try FileManager.default.moveItem(at: temporary, to: destination)
        record(LayaStageTiming(
            "compile",
            seconds: Date().timeIntervalSince(start),
            note: "\(LayaFormat.bytes(Self.directorySize(package))) package → \(LayaFormat.bytes(Self.directorySize(destination))) mlmodelc"
        ))
        return destination
    }

    /// Drops the loaded runtime but keeps the files, so **Load model** rebuilds
    /// it with the current compute units.
    func unload() {
        guard !phase.isBusy else { return }
        runtime = nil
        info = nil
        computePlan = nil
        benchmark = nil
        loadMemory = nil
        phase = .notDownloaded
        append("unloaded")
    }

    /// Removes the download and the compiled graph.
    func deleteModel() {
        guard !phase.isBusy else { return }
        unload()
        history = []
        stages = []
        try? FileManager.default.removeItem(at: baseDirectory)
        append("deleted \(baseDirectory.path)")
    }

    // MARK: Inference

    func predict(state: String, question: LayaQuestion) async throws -> LayaPrediction {
        guard let runtime else {
            throw LayaError.model("The model is not loaded.")
        }
        isPredicting = true
        defer { isPredicting = false }
        do {
            let prediction = try await Task.detached(priority: .userInitiated) {
                try runtime.predict(state: state, question: question)
            }.value
            history.append(prediction)
            if history.count > Self.historyLimit {
                history.removeFirst(history.count - Self.historyLimit)
            }
            let t = prediction.timings
            append(
                "predict \(question.kind.displayName) \(prediction.inputTokens) tok: total \(LayaFormat.seconds(t.total)) = prepare \(LayaFormat.seconds(t.prepare)) + host \(LayaFormat.seconds(t.hostTensors)) + pack \(LayaFormat.seconds(t.pack)) + graph \(LayaFormat.seconds(t.graph)) + head \(LayaFormat.seconds(t.head)); confidence \(prediction.decision.confidence)"
            )
            if history.count == 1 {
                append("graph outputs: \(prediction.outputSummary)")
            }
            return prediction
        } catch {
            let failure = LayaFailure(stage: "predict", error: error)
            append("predict FAILED " + failure.report.replacingOccurrences(of: "\n", with: " | "))
            throw error
        }
    }

    /// Prepared-sequence token count, or nil when the runtime is not loaded.
    func tokenCount(state: String, question: LayaQuestion) -> Result<Int, Error>? {
        guard let runtime else { return nil }
        return Result { try runtime.tokenCount(state: state, question: question) }
    }

    /// Runs the same question `runs` times and keeps order statistics.
    func runBenchmark(state: String, question: LayaQuestion, runs: Int = 10) async {
        guard runtime != nil, !isBenchmarking else { return }
        isBenchmarking = true
        defer { isBenchmarking = false }
        append("benchmark start: \(runs) runs, \(computeChoice.title), thermal \(LayaDeviceStats.label(for: ProcessInfo.processInfo.thermalState))")
        var timings: [LayaTimings] = []
        var tokens = 0
        do {
            for _ in 0..<runs {
                let prediction = try await predict(state: state, question: question)
                timings.append(prediction.timings)
                tokens = prediction.inputTokens
            }
        } catch {
            append("benchmark stopped after \(timings.count) runs")
        }
        guard !timings.isEmpty else { return }
        let report = LayaBenchmarkReport(runs: timings, inputTokens: tokens, computeUnits: computeChoice.title)
        benchmark = report
        append(report.text.replacingOccurrences(of: "\n", with: " | "))
        device = LayaDeviceStats.report()
    }

    /// Asks Core ML which device each graph operation prefers under the current units.
    func analyzeComputePlan() async {
        guard let compiledURL, !isPlanning else { return }
        isPlanning = true
        defer { isPlanning = false }
        let units = computeChoice.units
        do {
            let summary = try await Task.detached(priority: .utility) {
                try await LayaRuntime.computePlan(compiledModelURL: compiledURL, computeUnits: units)
            }.value
            computePlan = summary
            append(summary.text.replacingOccurrences(of: "\n", with: " | "))
        } catch {
            let failure = LayaFailure(stage: "compute plan", error: error)
            append("compute plan FAILED " + failure.report.replacingOccurrences(of: "\n", with: " | "))
        }
    }

    // MARK: Report

    /// Everything a remote debugger needs, as one pasteable text.
    func report() -> String {
        var sections: [String] = []
        sections.append("Laya diagnostics \(LayaFormat.timestamp(Date()))")
        sections.append("model \(LayaModelSource.repoID)@\(LayaModelSource.shortRevision); compute \(computeChoice.title)")
        sections.append(LayaDeviceStats.report().text)
        sections.append("phase: \(phaseText)")
        if let failure = phase.failure {
            sections.append(failure.report)
        }
        if !stages.isEmpty {
            sections.append("stages:\n" + stages.map { "  \($0.name): \(LayaFormat.seconds($0.seconds))" + ($0.note.map { " (\($0))" } ?? "") }.joined(separator: "\n"))
        }
        if let loadMemory {
            sections.append("resident memory: \(LayaFormat.bytes(loadMemory.before)) → \(LayaFormat.bytes(loadMemory.after)) around load")
        }
        if let info {
            sections.append(info.text)
        }
        if let computePlan {
            sections.append(computePlan.text)
        }
        if let graphStats, let totalStats {
            sections.append("history graph: \(graphStats.summary)\nhistory total: \(totalStats.summary)")
        }
        if let last = lastPrediction {
            sections.append("last prediction: " + last.timings.rows.map { "\($0.name) \(LayaFormat.seconds($0.seconds))" }.joined(separator: ", ") + "\noutputs: \(last.outputSummary)")
        }
        if let benchmark {
            sections.append(benchmark.text)
        }
        sections.append("log:\n" + log.text)
        return sections.joined(separator: "\n\n")
    }

    var phaseText: String {
        switch phase {
        case .notDownloaded: return isDownloaded ? "downloaded, not loaded" : "not downloaded"
        case .downloading(let fraction): return "downloading \(Int(fraction * 100))%"
        case .verifying: return "verifying"
        case .compiling: return "compiling"
        case .loading: return "loading"
        case .ready: return "ready"
        case .failed(let failure): return "failed in \(failure.stage)"
        }
    }

    // MARK: Files

    /// Bytes under `url`, or its own size when it is a file.
    static func directorySize(_ url: URL) -> Int64 {
        if let values = try? url.resourceValues(forKeys: [.fileSizeKey, .isRegularFileKey]), values.isRegularFile == true {
            return Int64(values.fileSize ?? 0)
        }
        guard let enumerator = FileManager.default.enumerator(at: url, includingPropertiesForKeys: [.fileSizeKey, .isRegularFileKey]) else {
            return 0
        }
        var total: Int64 = 0
        for case let file as URL in enumerator {
            let values = try? file.resourceValues(forKeys: [.fileSizeKey, .isRegularFileKey])
            if values?.isRegularFile == true {
                total += Int64(values?.fileSize ?? 0)
            }
        }
        return total
    }

    /// Top-level entries of `url` with sizes, one line.
    static func fileListing(_ url: URL) -> String {
        let entries = (try? FileManager.default.contentsOfDirectory(at: url, includingPropertiesForKeys: nil)) ?? []
        return entries.map(\.lastPathComponent).sorted().map { name in
            "\(name) \(LayaFormat.bytes(directorySize(url.appendingPathComponent(name))))"
        }.joined(separator: ", ")
    }
}

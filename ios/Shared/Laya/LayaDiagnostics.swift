import Foundation

// Everything here is plain Foundation so it builds and tests off-device. The
// Core ML and UIKit sides feed these types; the view and the copyable report
// render them.

/// How long one lifecycle stage took, with an optional note such as throughput.
struct LayaStageTiming: Equatable, Identifiable {
    let name: String
    let seconds: TimeInterval
    let note: String?

    var id: String { name }

    init(_ name: String, seconds: TimeInterval, note: String? = nil) {
        self.name = name
        self.seconds = seconds
        self.note = note
    }
}

/// Wall time of each step of one `predict` call.
struct LayaTimings: Equatable {
    /// Tokenize and lay out the prompt.
    var prepare: TimeInterval = 0
    /// Embedding gather, masks, marker map.
    var hostTensors: TimeInterval = 0
    /// Float16 `MLMultiArray` packing.
    var pack: TimeInterval = 0
    /// `MLModel.prediction`.
    var graph: TimeInterval = 0
    /// Output unpacking and the CPU action head.
    var head: TimeInterval = 0
    var total: TimeInterval = 0

    static let stageNames = ["prepare", "host tensors", "pack", "graph", "head", "total"]

    var values: [TimeInterval] { [prepare, hostTensors, pack, graph, head, total] }

    var rows: [(name: String, seconds: TimeInterval)] {
        Array(zip(Self.stageNames, values))
    }
}

/// Order statistics over a set of latency samples, in seconds.
struct LayaLatencyStats: Equatable {
    let count: Int
    let min: TimeInterval
    let median: TimeInterval
    let mean: TimeInterval
    let p95: TimeInterval
    let max: TimeInterval

    init?(_ samples: [TimeInterval]) {
        guard !samples.isEmpty else { return nil }
        let sorted = samples.sorted()
        count = sorted.count
        min = sorted[0]
        max = sorted[sorted.count - 1]
        mean = sorted.reduce(0, +) / Double(sorted.count)
        median = Self.percentile(sorted, 0.5)
        p95 = Self.percentile(sorted, 0.95)
    }

    /// Nearest-rank percentile over an ascending array.
    static func percentile(_ sorted: [TimeInterval], _ fraction: Double) -> TimeInterval {
        let rank = Int((Double(sorted.count) * fraction).rounded(.up))
        return sorted[Swift.max(0, Swift.min(sorted.count - 1, rank - 1))]
    }

    var summary: String {
        "n=\(count) min \(LayaFormat.seconds(min)) · median \(LayaFormat.seconds(median)) · p95 \(LayaFormat.seconds(p95)) · max \(LayaFormat.seconds(max))"
    }
}

/// Repeated runs of one question. The first run is reported alone because it
/// usually carries the Neural Engine warm-up.
struct LayaBenchmarkReport: Equatable {
    let runs: [LayaTimings]
    let inputTokens: Int
    let computeUnits: String

    var first: LayaTimings? { runs.first }

    /// Steady-state samples: every run after the first, or all runs if there is only one.
    var steady: [LayaTimings] {
        runs.count > 1 ? Array(runs.dropFirst()) : runs
    }

    func stats(_ stage: (LayaTimings) -> TimeInterval) -> LayaLatencyStats? {
        LayaLatencyStats(steady.map(stage))
    }

    var text: String {
        var lines = ["Benchmark: \(runs.count) runs, \(inputTokens) input tokens, \(computeUnits)"]
        if let first {
            lines.append("first run: total \(LayaFormat.seconds(first.total)), graph \(LayaFormat.seconds(first.graph))")
        }
        let stages: [(String, (LayaTimings) -> TimeInterval)] = [
            ("prepare", \.prepare), ("host tensors", \.hostTensors), ("pack", \.pack),
            ("graph", \.graph), ("head", \.head), ("total", \.total),
        ]
        for (name, stage) in stages {
            if let stats = stats(stage) {
                lines.append("\(name): \(stats.summary)")
            }
        }
        return lines.joined(separator: "\n")
    }
}

/// A failure with enough context to debug from a pasted report.
struct LayaFailure: Equatable {
    /// The lifecycle stage that was running, for example `download` or `predict`.
    let stage: String
    /// One line for the status row.
    let message: String
    /// Underlying error chain, domains and codes, file paths.
    let details: [String]
    let date: Date

    init(stage: String, message: String, details: [String] = [], date: Date = Date()) {
        self.stage = stage
        self.message = message
        self.details = details
        self.date = date
    }

    /// Unwraps `error` and its `NSUnderlyingErrorKey` chain.
    init(stage: String, error: Error, date: Date = Date()) {
        var details: [String] = []
        var message: String
        if let laya = error as? LayaError {
            message = laya.errorDescription ?? "Unknown error"
            details.append("LayaError.\(laya.caseName)")
        } else {
            message = error.localizedDescription
        }
        var current: NSError? = error as NSError
        var depth = 0
        while let nsError = current, depth < 6 {
            var line = "\(nsError.domain) code \(nsError.code)"
            if depth > 0 {
                line = "underlying: " + line + " — " + nsError.localizedDescription
            }
            details.append(line)
            for key in [NSLocalizedFailureReasonErrorKey, NSLocalizedRecoverySuggestionErrorKey, NSFilePathErrorKey, NSURLErrorKey, NSDebugDescriptionErrorKey] {
                if let value = nsError.userInfo[key] {
                    details.append("\(key): \(value)")
                }
            }
            current = nsError.userInfo[NSUnderlyingErrorKey] as? NSError
            depth += 1
        }
        if (error as NSError).domain == NSURLErrorDomain {
            message = "Download failed: \(message)"
        }
        self.init(stage: stage, message: message, details: details, date: date)
    }

    var report: String {
        (["[\(stage)] \(message)"] + details.map { "  " + $0 }).joined(separator: "\n")
    }
}

extension LayaError {
    /// The enum case without payload, for reports.
    var caseName: String {
        switch self {
        case .invalidQuestion: return "invalidQuestion"
        case .tooManyOptions: return "tooManyOptions"
        case .tooManyTokens: return "tooManyTokens"
        case .optionBudgetExceeded: return "optionBudgetExceeded"
        case .bundle: return "bundle"
        case .model: return "model"
        }
    }
}

/// One timestamped diagnostics line.
struct LayaLogEntry: Equatable {
    let date: Date
    let message: String

    var line: String { "\(LayaFormat.timestamp(date)) \(message)" }
}

/// Bounded, newest-last log. The store mirrors appends to disk.
struct LayaLogBuffer: Equatable {
    private(set) var entries: [LayaLogEntry] = []
    let limit: Int

    init(limit: Int = 400) {
        self.limit = limit
    }

    mutating func append(_ message: String, date: Date = Date()) {
        entries.append(LayaLogEntry(date: date, message: message))
        if entries.count > limit {
            entries.removeFirst(entries.count - limit)
        }
    }

    /// Restores lines written by `LayaLogEntry.line`; unparseable lines keep `date`.
    mutating func restore(from text: String, fallbackDate: Date = Date()) {
        for raw in text.split(whereSeparator: \.isNewline) {
            let line = String(raw)
            guard !line.isEmpty else { continue }
            if line.count > 24, line[line.index(line.startIndex, offsetBy: 24)] == " ",
               let date = LayaFormat.parseTimestamp(String(line.prefix(24))) {
                entries.append(LayaLogEntry(date: date, message: String(line.dropFirst(25))))
            } else {
                entries.append(LayaLogEntry(date: fallbackDate, message: line))
            }
        }
        if entries.count > limit {
            entries.removeFirst(entries.count - limit)
        }
    }

    var text: String { entries.map(\.line).joined(separator: "\n") }

    func tail(_ count: Int) -> [LayaLogEntry] { Array(entries.suffix(count)) }
}

/// One Core ML feature: name, shape, and element type.
struct LayaFeatureDescription: Equatable {
    let name: String
    let shape: [Int]
    let dataType: String

    var line: String { "\(name): \(shape) \(dataType)" }
}

/// The compiled graph's inputs and outputs as Core ML reports them.
struct LayaSignature: Equatable {
    let inputs: [LayaFeatureDescription]
    let outputs: [LayaFeatureDescription]

    var text: String {
        (["inputs:"] + inputs.map { "  " + $0.line } + ["outputs:"] + outputs.map { "  " + $0.line })
            .joined(separator: "\n")
    }
}

/// Where each operation of the compiled program is expected to run.
struct LayaComputePlanSummary: Equatable {
    static let neuralEngine = "Neural Engine"
    static let cpu = "CPU"
    static let gpu = "GPU"

    let operationCount: Int
    /// Operation count by preferred device label.
    let operationsByDevice: [String: Int]
    /// Estimated cost weight by preferred device label (sums to about 1).
    let costByDevice: [String: Double]
    /// Operator names that do not prefer the Neural Engine, with counts.
    let offNeuralEngineOperators: [String: Int]
    /// Operations Core ML returned no device usage for.
    let unplanned: Int
    let seconds: TimeInterval

    var neuralEngineShare: Double {
        guard operationCount > 0 else { return 0 }
        return Double(operationsByDevice[Self.neuralEngine] ?? 0) / Double(operationCount)
    }

    var headline: String {
        let ane = operationsByDevice[Self.neuralEngine] ?? 0
        return "\(ane) of \(operationCount) ops prefer the Neural Engine (\(LayaFormat.percent(neuralEngineShare)))"
    }

    var deviceRows: [(device: String, operations: Int, cost: Double)] {
        let devices = Set(operationsByDevice.keys).union(costByDevice.keys)
        return devices.sorted { (operationsByDevice[$0] ?? 0) > (operationsByDevice[$1] ?? 0) }
            .map { ($0, operationsByDevice[$0] ?? 0, costByDevice[$0] ?? 0) }
    }

    /// Off-ANE operators, most frequent first.
    var fallbackRows: [(operator: String, count: Int)] {
        offNeuralEngineOperators.sorted { $0.value > $1.value || ($0.value == $1.value && $0.key < $1.key) }
            .map { ($0.key, $0.value) }
    }

    var text: String {
        var lines = ["Compute plan (\(LayaFormat.seconds(seconds))): \(headline)"]
        for row in deviceRows {
            lines.append("  \(row.device): \(row.operations) ops, cost \(LayaFormat.percent(row.cost))")
        }
        if unplanned > 0 {
            lines.append("  no device usage reported: \(unplanned) ops")
        }
        if !fallbackRows.isEmpty {
            lines.append("  off Neural Engine: " + fallbackRows.map { "\($0.operator)×\($0.count)" }.joined(separator: ", "))
        }
        return lines.joined(separator: "\n")
    }
}

/// Number formatting shared by the view, the log, and the report.
enum LayaFormat {
    static func seconds(_ value: TimeInterval) -> String {
        if value < 0.001 { return String(format: "%.0f µs", value * 1_000_000) }
        if value < 1 { return String(format: "%.1f ms", value * 1000) }
        return String(format: "%.2f s", value)
    }

    static func percent(_ value: Double) -> String {
        String(format: "%.1f%%", value * 100)
    }

    static func bytes(_ value: Int64) -> String {
        let units = ["B", "KB", "MB", "GB"]
        var scaled = Double(value)
        var index = 0
        while scaled >= 1000, index < units.count - 1 {
            scaled /= 1000
            index += 1
        }
        return index == 0 ? "\(value) B" : String(format: "%.1f", scaled) + " " + units[index]
    }

    static func throughput(bytes: Int64, seconds: TimeInterval) -> String {
        guard seconds > 0 else { return "—" }
        return Self.bytes(Int64(Double(bytes) / seconds)) + "/s"
    }

    private static let timestampFormatter: DateFormatter = {
        let formatter = DateFormatter()
        formatter.locale = Locale(identifier: "en_US_POSIX")
        formatter.timeZone = TimeZone(secondsFromGMT: 0)
        formatter.dateFormat = "yyyy-MM-dd'T'HH:mm:ss.SSS'Z'"
        return formatter
    }()

    /// `2026-09-20T19:34:05.123Z`, always 24 characters.
    static func timestamp(_ date: Date) -> String {
        timestampFormatter.string(from: date)
    }

    static func parseTimestamp(_ text: String) -> Date? {
        timestampFormatter.date(from: text)
    }
}

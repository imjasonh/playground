import Foundation
@testable import Playground

/// Replays OCR readings of the moving-sign clip through the pipeline with a
/// fake model, and scores how each line on the sign held its translation.
struct LiveTranslateClipReplay {
    /// The four main lines in `Fixtures/LiveTranslate/moving-sign.mp4`. The
    /// clip also has fine print and a room plate that OCR reads unreliably on
    /// purpose; those aren't scored.
    static let signLines = [
        "SALIDA DE EMERGENCIA",
        "Mantenga la puerta cerrada",
        "Prohibido fumar",
        "Solo personal autorizado",
    ]
    /// Latest pass for a line's first translation. The first batch starts once
    /// two passes read the sign, and the fake model answers within a few more.
    static let latestFirstTranslation = 12
    /// Share of later passes that read a line and must show its translation.
    static let minimumShownShare = 0.9
    static let maximumTranslationsPerLine = 2
    static let maximumBatchesPerLine = 2

    struct LineResult {
        let line: String
        let firstTranslatedPass: Int?
        /// Passes after the first translation that read this line.
        let laterReads: Int
        /// Of those, passes whose overlay showed a translation.
        let laterShown: Int
        let translations: Set<String>
        let batches: Int
    }

    let passes: [[LiveTranslateObservation]]
    let history: [[LiveTranslateOverlay]]
    let batches: [LiveTranslatePipeline.Batch]
    let results: [LineResult]

    init(passes: [[LiveTranslateObservation]]) {
        var pipeline = LiveTranslatePipeline()
        var model = LiveTranslateFakeModel()
        var history: [[LiveTranslateOverlay]] = []
        for (pass, observations) in passes.enumerated() {
            model.step(pass: pass, observations: observations, pipeline: &pipeline)
            history.append(pipeline.overlays)
        }
        self.passes = passes
        self.history = history
        batches = model.started
        results = Self.signLines.map { line in
            let overlays = history.map { pass in pass.first { Self.isSameLine($0.sourceText, line) } }
            let first = overlays.firstIndex { $0?.isTranslated == true }
            let later = passes.indices.filter { pass in
                guard let first, pass > first else { return false }
                return passes[pass].contains { Self.isSameLine($0.text, line) }
            }
            return LineResult(
                line: line,
                firstTranslatedPass: first,
                laterReads: later.count,
                laterShown: later.filter { overlays[$0]?.isTranslated == true }.count,
                translations: Set(overlays.compactMap { $0?.isTranslated == true ? $0?.displayText : nil }),
                batches: model.started.filter { batch in batch.sources.contains { Self.isSameLine($0, line) } }.count
            )
        }
    }

    /// Problems worth failing a test over. Empty when every line held up.
    var failures: [String] {
        results.flatMap { result -> [String] in
            guard let first = result.firstTranslatedPass else {
                return ["\(result.line): never translated"]
            }
            var problems: [String] = []
            if first > Self.latestFirstTranslation {
                problems.append("\(result.line): first translated at pass \(first)")
            }
            if Double(result.laterShown) < Self.minimumShownShare * Double(result.laterReads) {
                problems.append("\(result.line): translated on \(result.laterShown) of \(result.laterReads) later reads")
            }
            if result.translations.count > Self.maximumTranslationsPerLine {
                problems.append("\(result.line): showed \(result.translations.sorted())")
            }
            if result.batches > Self.maximumBatchesPerLine {
                problems.append("\(result.line): sent to the model \(result.batches) times")
            }
            return problems
        }
    }

    /// What OCR read and what the overlays showed on each pass, for failure messages.
    var transcript: String {
        var lines: [String] = []
        for (pass, observations) in passes.enumerated() {
            let read = observations.map(\.text).joined(separator: " | ")
            let shown = history[pass]
                .map { $0.isTranslated ? "[\($0.displayText)]" : "(\($0.sourceText))" }
                .joined(separator: " ")
            lines.append("pass \(pass): read \(read.isEmpty ? "nothing" : read) -> \(shown)")
        }
        lines.append("batches: \(batches.map(\.sources))")
        return lines.joined(separator: "\n")
    }

    static func isSameLine(_ reading: String, _ line: String) -> Bool {
        LiveTranslateText.similarity(LiveTranslateText.matchKey(reading), LiveTranslateText.matchKey(line)) >= 0.7
    }
}

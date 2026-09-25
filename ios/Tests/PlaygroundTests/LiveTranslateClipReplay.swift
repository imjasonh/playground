import CoreGraphics
import Foundation
@testable import Playground

/// Where each main line of the moving-sign clip sits in every frame, written by
/// `ios/scripts/make-live-translate-clip.py` next to the clip.
struct LiveTranslateClipTruth: Decodable {
    let fps: Int
    let width: Int
    let height: Int
    /// The main sign lines. The clip also has fine print and a room plate that
    /// OCR reads unreliably on purpose; those aren't scored.
    let lines: [String]
    /// Per frame, per line: `[x, y, width, height]`, Vision-normalized.
    let boxes: [[[Double]]]

    static func load(from url: URL) throws -> LiveTranslateClipTruth {
        try JSONDecoder().decode(LiveTranslateClipTruth.self, from: Data(contentsOf: url))
    }

    func box(line: Int, frame: Int) -> CGRect {
        let values = boxes[frame][line]
        return CGRect(x: values[0], y: values[1], width: values[2], height: values[3])
    }
}

/// Replays OCR readings of the moving-sign clip through the pipeline with a
/// fake model, and scores how each line on the sign held its translation.
struct LiveTranslateClipReplay {
    /// Latest pass for a line's first translation. The first batch starts once
    /// two passes read the sign, and the fake model answers within a few more.
    static let latestFirstTranslation = 12
    /// Share of later passes that read a line and must show its translation.
    static let minimumShownShare = 0.9
    static let maximumTranslationsPerLine = 2
    static let maximumBatchesPerLine = 2
    /// Largest change in a card's height between translated passes, beyond
    /// the line's own change on screen. Bigger reads as the text jumping.
    static let maximumSizeJump = 0.12
    /// Share of the line's width a translated card must cover.
    static let minimumCoverage = 0.85

    struct LineResult {
        let line: String
        let firstTranslatedPass: Int?
        /// Passes after the first translation that read this line.
        let laterReads: Int
        /// Of those, passes whose overlay showed a translation.
        let laterShown: Int
        let translations: Set<String>
        let batches: Int
        /// Largest pass-to-pass change in card height relative to the line's true height.
        let largestSizeJump: Double
        /// Smallest share of the line's true width a translated card covered.
        let smallestCoverage: Double
    }

    let passes: [[LiveTranslateObservation]]
    let history: [[LiveTranslateOverlay]]
    let batches: [LiveTranslatePipeline.Batch]
    let results: [LineResult]

    /// `passes[i]` is the OCR reading of clip frame `i * frameStride`.
    init(passes: [[LiveTranslateObservation]], truth: LiveTranslateClipTruth, frameStride: Int) {
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
        results = truth.lines.enumerated().map { lineIndex, line in
            let overlays = history.map { pass in pass.first { Self.isSameLine($0.sourceText, line) } }
            let first = overlays.firstIndex { $0?.isTranslated == true }
            let later = passes.indices.filter { pass in
                guard let first, pass > first else { return false }
                return passes[pass].contains { Self.isSameLine($0.text, line) }
            }
            var ratios: [Double] = []
            var smallestCoverage = 1.0
            for (pass, overlay) in overlays.enumerated() {
                guard let overlay, overlay.isTranslated else { continue }
                let actual = truth.box(line: lineIndex, frame: pass * frameStride)
                let card = overlay.boundingBox
                ratios.append(Double(card.height / actual.height))
                let covered = min(card.maxX, actual.maxX) - max(card.minX, actual.minX)
                smallestCoverage = min(smallestCoverage, Double(max(covered, 0) / actual.width))
            }
            let jumps = zip(ratios, ratios.dropFirst()).map { abs($1 / $0 - 1) }
            return LineResult(
                line: line,
                firstTranslatedPass: first,
                laterReads: later.count,
                laterShown: later.filter { overlays[$0]?.isTranslated == true }.count,
                translations: Set(overlays.compactMap { $0?.isTranslated == true ? $0?.displayText : nil }),
                batches: model.started.filter { batch in batch.sources.contains { Self.isSameLine($0, line) } }.count,
                largestSizeJump: jumps.max() ?? 0,
                smallestCoverage: smallestCoverage
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
            if result.largestSizeJump > Self.maximumSizeJump {
                problems.append("\(result.line): card height jumped \(Int(result.largestSizeJump * 100))% between passes")
            }
            if result.smallestCoverage < Self.minimumCoverage {
                problems.append("\(result.line): card covered only \(Int(result.smallestCoverage * 100))% of the line")
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

/// Plays the moving-sign clip frame by frame the way the session runs: OCR
/// reads every `frameStride`th frame, its result arrives `latency` frames
/// later, and the follower moves the overlays on every frame. Scores how far
/// each overlay sits from where its line really is.
struct LiveTranslateFollowReplay {
    /// Distance, in clip pixels, that 95% of a line's overlay placements stay
    /// within. Overlays left where OCR put them sit 45 to 72 pixels off.
    static let maximumTypicalDrift = 12.0
    /// Distance no placement may exceed.
    static let maximumDrift = 30.0
    /// Largest frame-to-frame change in overlay height, beyond the line's own change.
    static let maximumSizeStep = 0.1

    struct LineResult {
        let line: String
        /// Frames that placed an overlay on this line.
        let frames: Int
        /// 95th percentile of the distance from the line's true center, in clip pixels.
        let typicalDrift: Double
        let largestDrift: Double
        let largestSizeStep: Double
    }

    /// Per frame, the overlays shown: source text and box.
    let placements: [[(text: String, box: CGRect)]]
    let results: [LineResult]

    init(
        frames: [LiveTranslateGrayFrame],
        passes: [[LiveTranslateObservation]],
        truth: LiveTranslateClipTruth,
        frameStride: Int,
        latency: Int
    ) {
        var pipeline = LiveTranslatePipeline(language: .english)
        var follower = LiveTranslateFollower()
        var pending: [(due: Int, frame: Int)] = []
        var placements: [[(text: String, box: CGRect)]] = []
        for (number, frame) in frames.enumerated() {
            follower.advance(to: frame, number: number)
            if number % frameStride == 0, number / frameStride < passes.count {
                follower.hold(frame, for: number)
                pending.append((number + latency, number))
            }
            while let next = pending.first, next.due <= number {
                pending.removeFirst()
                pipeline.ingest(passes[next.frame / frameStride])
                follower.rebase(
                    Dictionary(uniqueKeysWithValues: pipeline.overlays.map { ($0.id, $0.boundingBox) }),
                    from: next.frame
                )
            }
            let positions = follower.positions
            placements.append(pipeline.overlays.compactMap { overlay in
                positions[overlay.id].map { (overlay.sourceText, $0) }
            })
        }
        self.placements = placements

        let width = Double(truth.width)
        let height = Double(truth.height)
        results = truth.lines.enumerated().map { lineIndex, line in
            var drifts: [Double] = []
            var steps: [Double] = []
            var previousRatio: Double?
            for (number, shown) in placements.enumerated() {
                guard let box = shown.first(where: { LiveTranslateClipReplay.isSameLine($0.text, line) })?.box else {
                    previousRatio = nil
                    continue
                }
                let actual = truth.box(line: lineIndex, frame: number)
                drifts.append(hypot(
                    Double(box.midX - actual.midX) * width,
                    Double(box.midY - actual.midY) * height
                ))
                let ratio = Double(box.height / actual.height)
                if let previousRatio {
                    steps.append(abs(ratio / previousRatio - 1))
                }
                previousRatio = ratio
            }
            let sorted = drifts.sorted()
            return LineResult(
                line: line,
                frames: drifts.count,
                typicalDrift: sorted.isEmpty ? 0 : sorted[min(sorted.count - 1, sorted.count * 95 / 100)],
                largestDrift: sorted.last ?? 0,
                largestSizeStep: steps.max() ?? 0
            )
        }
    }

    var failures: [String] {
        results.flatMap { result -> [String] in
            var problems: [String] = []
            if result.frames == 0 {
                problems.append("\(result.line): never placed an overlay")
            }
            if result.typicalDrift > Self.maximumTypicalDrift {
                problems.append("\(result.line): 95% of overlays within \(Int(result.typicalDrift)) px of the line")
            }
            if result.largestDrift > Self.maximumDrift {
                problems.append("\(result.line): an overlay landed \(Int(result.largestDrift)) px from the line")
            }
            if result.largestSizeStep > Self.maximumSizeStep {
                problems.append("\(result.line): overlay height stepped \(Int(result.largestSizeStep * 100))% in one frame")
            }
            return problems
        }
    }

    var summary: String {
        results.map { result in
            let typical = String(format: "%.1f", result.typicalDrift)
            let worst = String(format: "%.1f", result.largestDrift)
            let step = String(format: "%.1f", result.largestSizeStep * 100)
            return "\(result.line): \(result.frames) frames, 95% within \(typical) px, worst \(worst) px, "
                + "largest size step \(step)%"
        }.joined(separator: "\n")
    }
}

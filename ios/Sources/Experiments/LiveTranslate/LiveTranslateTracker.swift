import CoreGraphics
import Foundation

/// One OCR line followed across frames.
struct LiveTranslateTrack: Equatable, Identifiable {
    /// Stays the same while the line stays in view.
    let id: String
    /// Normalized reading with the most weighted votes across recent passes.
    var text: String
    /// `LiveTranslateText.matchKey(text)`.
    var key: String
    /// Vision-normalized box (origin bottom-left). After a missed pass, the last
    /// box moved by the camera shift.
    var boundingBox: CGRect
    /// OCR passes that matched this line.
    var hits: Int
    /// Consecutive OCR passes that missed this line.
    var misses: Int
    /// Decaying confidence per normalized reading. The leader becomes `text`.
    var votes: [String: Double]

    /// Read in enough passes to be worth a model call.
    var isSettled: Bool {
        hits >= LiveTranslateTracker.settleHits
    }
}

/// Pairs each OCR pass with the lines it continues, so a line keeps one id
/// while the camera moves, Vision rereads it a little differently, or a pass
/// misses it.
///
/// Every pass first estimates the camera shift from readings that match an
/// existing line almost exactly, and moves every line by it. A reading then
/// continues a line when it has similar text near the moved box, or similar
/// text over the same spot. A settled line that no reading continues survives
/// two passes, so one missed OCR pass doesn't make its overlay flicker.
struct LiveTranslateTracker {
    /// Passes a line must match before it earns a model call or an untranslated outline.
    static let settleHits = 2
    /// Consecutive missed passes a settled line survives.
    static let maximumMisses = 2
    /// Weight an older reading keeps each pass, so a reading that changes for
    /// good takes over after two passes.
    static let voteDecay = 0.7
    /// Text similarity that continues a line anywhere near its moved box.
    static let sameTextSimilarity = 0.8
    /// Text similarity that continues a line when the boxes overlap.
    static let rereadSimilarity = 0.5
    /// Intersection over union that counts as the same spot.
    static let rereadOverlap = 0.3
    /// Readings at least this similar to a line vote on the camera shift.
    static let anchorSimilarity = 0.9
    /// Largest per-pass camera shift trusted, in normalized image units.
    static let maximumShift = 0.5

    private(set) var tracks: [LiveTranslateTrack] = []
    private var serial = 0

    mutating func reset() {
        tracks = []
    }

    mutating func update(with observations: [LiveTranslateObservation]) {
        let readings = observations.compactMap(Reading.init)
        let similarity = tracks.map { track in
            readings.map { LiveTranslateText.similarity(track.key, $0.key) }
        }
        let shift = Self.cameraShift(tracks: tracks, readings: readings, similarity: similarity)
        let predicted = tracks.map { $0.boundingBox.offsetBy(dx: shift.dx, dy: shift.dy) }

        var pairs: [(track: Int, reading: Int, score: Double)] = []
        for trackIndex in tracks.indices {
            for readingIndex in readings.indices {
                if let score = Self.matchScore(
                    similarity: similarity[trackIndex][readingIndex],
                    predicted: predicted[trackIndex],
                    reading: readings[readingIndex].box
                ) {
                    pairs.append((trackIndex, readingIndex, score))
                }
            }
        }
        pairs.sort { lhs, rhs in
            if lhs.score != rhs.score { return lhs.score > rhs.score }
            if lhs.track != rhs.track { return lhs.track < rhs.track }
            return lhs.reading < rhs.reading
        }

        var readingForTrack = [Int?](repeating: nil, count: tracks.count)
        var trackForReading = [Int?](repeating: nil, count: readings.count)
        for pair in pairs where readingForTrack[pair.track] == nil && trackForReading[pair.reading] == nil {
            readingForTrack[pair.track] = pair.reading
            trackForReading[pair.reading] = pair.track
        }

        var next: [LiveTranslateTrack] = []
        for trackIndex in tracks.indices {
            var track = tracks[trackIndex]
            if let readingIndex = readingForTrack[trackIndex] {
                track.absorb(readings[readingIndex])
            } else {
                track.misses += 1
                track.boundingBox = predicted[trackIndex]
                // A reading seen once and then lost is usually OCR noise.
                guard track.isSettled, track.misses <= Self.maximumMisses else { continue }
            }
            next.append(track)
        }
        for readingIndex in readings.indices where trackForReading[readingIndex] == nil {
            serial += 1
            next.append(LiveTranslateTrack(id: "line-\(serial)", reading: readings[readingIndex]))
        }

        // A missed line under a settled reading was reread as different text
        // (or split or merged). A one-pass reading doesn't count, so OCR noise
        // can't knock out a line that is still there.
        let settled = next.filter { $0.misses == 0 && $0.isSettled }.map(\.boundingBox)
        let frame = CGRect(x: 0, y: 0, width: 1, height: 1)
        next.removeAll { track in
            guard track.misses > 0 else { return false }
            guard track.boundingBox.intersects(frame) else { return true }
            return settled.contains { Self.covers(track.boundingBox, $0) }
        }
        next.sort { LiveTranslateResultBuilder.readsBefore($0.boundingBox, $1.boundingBox) }
        tracks = next
    }

    static func voteWeight(confidence: Double) -> Double {
        max(confidence, 0.1)
    }

    /// Median displacement between readings and the nearest line with nearly identical text.
    private static func cameraShift(
        tracks: [LiveTranslateTrack],
        readings: [Reading],
        similarity: [[Double]]
    ) -> (dx: CGFloat, dy: CGFloat) {
        var dxs: [CGFloat] = []
        var dys: [CGFloat] = []
        for (readingIndex, reading) in readings.enumerated() {
            var nearest: (distance: CGFloat, dx: CGFloat, dy: CGFloat)?
            for (trackIndex, track) in tracks.enumerated() {
                guard similarity[trackIndex][readingIndex] >= anchorSimilarity else { continue }
                let dx = reading.box.midX - track.boundingBox.midX
                let dy = reading.box.midY - track.boundingBox.midY
                guard abs(dx) <= maximumShift, abs(dy) <= maximumShift else { continue }
                let distance = hypot(dx, dy)
                if nearest.map({ distance < $0.distance }) ?? true {
                    nearest = (distance, dx, dy)
                }
            }
            if let nearest {
                dxs.append(nearest.dx)
                dys.append(nearest.dy)
            }
        }
        guard !dxs.isEmpty else { return (0, 0) }
        return (median(dxs), median(dys))
    }

    private static func median(_ values: [CGFloat]) -> CGFloat {
        let sorted = values.sorted()
        return sorted[sorted.count / 2]
    }

    private static func matchScore(similarity: Double, predicted: CGRect, reading: CGRect) -> Double? {
        let overlap = intersectionOverUnion(predicted, reading)
        if similarity >= sameTextSimilarity, isNear(predicted, reading) {
            // Same text beats a reread in place.
            return 2 + similarity + overlap
        }
        if similarity >= rereadSimilarity, overlap >= rereadOverlap {
            return similarity + overlap
        }
        return nil
    }

    /// Centers within one line width across and two line heights up or down.
    /// The camera shift can't remove the spread from a zoom, so the gate is loose.
    private static func isNear(_ lhs: CGRect, _ rhs: CGRect) -> Bool {
        let width = max(lhs.width, rhs.width)
        let height = max(lhs.height, rhs.height)
        return abs(lhs.midX - rhs.midX) <= width
            && abs(lhs.midY - rhs.midY) <= height * 2
    }

    private static func intersectionOverUnion(_ lhs: CGRect, _ rhs: CGRect) -> Double {
        let intersection = lhs.intersection(rhs)
        guard !intersection.isNull else { return 0 }
        let shared = intersection.width * intersection.height
        let union = lhs.width * lhs.height + rhs.width * rhs.height - shared
        guard union > 0 else { return 0 }
        return Double(shared / union)
    }

    /// Whether the boxes share more than half of the smaller one, as when one
    /// reading of a line replaces another or a line splits in two.
    static func covers(_ lhs: CGRect, _ rhs: CGRect) -> Bool {
        let intersection = lhs.intersection(rhs)
        guard !intersection.isNull else { return false }
        let smaller = min(lhs.width * lhs.height, rhs.width * rhs.height)
        guard smaller > 0 else { return false }
        return intersection.width * intersection.height / smaller > 0.5
    }
}

/// One OCR observation, normalized for matching.
private struct Reading {
    let text: String
    let key: String
    let confidence: Double
    let box: CGRect

    init?(_ observation: LiveTranslateObservation) {
        let text = LiveTranslateResultBuilder.normalize(observation.text)
        guard !text.isEmpty else { return nil }
        self.text = text
        key = LiveTranslateText.matchKey(text)
        confidence = observation.confidence
        box = observation.boundingBox
    }
}

private extension LiveTranslateTrack {
    init(id: String, reading: Reading) {
        self.init(
            id: id,
            text: reading.text,
            key: reading.key,
            boundingBox: reading.box,
            hits: 1,
            misses: 0,
            votes: [reading.text: LiveTranslateTracker.voteWeight(confidence: reading.confidence)]
        )
    }

    mutating func absorb(_ reading: Reading) {
        var tally = votes
            .mapValues { $0 * LiveTranslateTracker.voteDecay }
            .filter { $0.value >= 0.05 }
        tally[reading.text, default: 0] += LiveTranslateTracker.voteWeight(confidence: reading.confidence)
        votes = tally
        if let leader = tally.max(by: { ($0.value, $0.key) < ($1.value, $1.key) })?.key,
           leader != text
        {
            text = leader
            key = LiveTranslateText.matchKey(leader)
        }
        boundingBox = reading.box
        hits += 1
        misses = 0
    }
}

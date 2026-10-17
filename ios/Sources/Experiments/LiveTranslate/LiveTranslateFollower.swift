import CoreGraphics
import Foundation

/// A small grayscale copy of a camera frame, for following text between OCR passes.
struct LiveTranslateGrayFrame: Equatable {
    let width: Int
    let height: Int
    /// Luminance, row by row from the top.
    let pixels: [UInt8]

    /// Half the width and height, each pixel the average of a 2×2 block.
    func halved() -> LiveTranslateGrayFrame {
        let halfWidth = width / 2
        let halfHeight = height / 2
        var result = [UInt8](repeating: 0, count: halfWidth * halfHeight)
        pixels.withUnsafeBufferPointer { source in
            for y in 0..<halfHeight {
                let top = 2 * y * width
                let bottom = top + width
                for x in 0..<halfWidth {
                    let sum = Int(source[top + 2 * x]) + Int(source[top + 2 * x + 1])
                        + Int(source[bottom + 2 * x]) + Int(source[bottom + 2 * x + 1])
                    result[y * halfWidth + x] = UInt8((sum + 2) / 4)
                }
            }
        }
        return LiveTranslateGrayFrame(width: halfWidth, height: halfHeight, pixels: result)
    }
}

extension LiveTranslateGrayFrame {
    /// Scales `image` so its longer side is `longSide` pixels and keeps its luminance.
    init?(image: CGImage, longSide: Int) {
        guard image.width > 0, image.height > 0, longSide > 0 else { return nil }
        let scale = Double(longSide) / Double(max(image.width, image.height))
        let width = max(1, Int((Double(image.width) * scale).rounded()))
        let height = max(1, Int((Double(image.height) * scale).rounded()))
        var pixels = [UInt8](repeating: 0, count: width * height)
        let drawn = pixels.withUnsafeMutableBytes { buffer -> Bool in
            guard let context = CGContext(
                data: buffer.baseAddress,
                width: width,
                height: height,
                bitsPerComponent: 8,
                bytesPerRow: width,
                space: CGColorSpaceCreateDeviceGray(),
                bitmapInfo: CGImageAlphaInfo.none.rawValue
            ) else { return false }
            context.interpolationQuality = .medium
            context.draw(image, in: CGRect(x: 0, y: 0, width: width, height: height))
            return true
        }
        guard drawn else { return nil }
        self.init(width: width, height: height, pixels: pixels)
    }
}

/// Luminance of one line sampled on a grid, normalized to zero mean and unit
/// length so a match ignores changes in brightness and contrast.
struct LiveTranslatePatch {
    /// Sample positions relative to the patch center, in pixels at zoom 1.
    let offsets: [(x: Int, y: Int)]
    let values: [Float]
    /// How much of the patch's contrast sits between neighboring samples.
    /// Blur lowers it.
    let sharpness: Float

    /// Samples `frame` over a box of `size` around `center`, padded to take in
    /// the background above and below the line. Nil when the patch leaves the
    /// frame or is nearly flat.
    init?(frame: LiveTranslateGrayFrame, center: (x: Int, y: Int), size: CGSize) {
        let width = max(size.width * 1.1, 8)
        let height = max(size.height * 1.8, 6)
        let columns = min(40, max(4, Int(width / 2)))
        let rows = min(12, max(3, Int(height / 1.5)))
        var offsets: [(x: Int, y: Int)] = []
        var samples: [Float] = []
        offsets.reserveCapacity(columns * rows)
        samples.reserveCapacity(columns * rows)
        for row in 0..<rows {
            let dy = Int(((CGFloat(row) + 0.5) * height / CGFloat(rows) - height / 2).rounded())
            let y = center.y + dy
            guard y >= 0, y < frame.height else { return nil }
            for column in 0..<columns {
                let dx = Int(((CGFloat(column) + 0.5) * width / CGFloat(columns) - width / 2).rounded())
                let x = center.x + dx
                guard x >= 0, x < frame.width else { return nil }
                offsets.append((x: dx, y: dy))
                samples.append(Float(frame.pixels[y * frame.width + x]))
            }
        }
        let mean = samples.reduce(0, +) / Float(samples.count)
        let centered = samples.map { $0 - mean }
        let norm = centered.reduce(0) { $0 + $1 * $1 }.squareRoot()
        // Less than about three gray levels of spread leaves nothing to lock onto.
        guard norm > 3 * Float(samples.count).squareRoot() else { return nil }
        let values = centered.map { $0 / norm }
        var sharpness: Float = 0
        for row in 0..<rows {
            for column in 1..<columns {
                let step = values[row * columns + column] - values[row * columns + column - 1]
                sharpness += step * step
            }
        }
        self.offsets = offsets
        self.values = values
        self.sharpness = sharpness
    }

    /// The patch laid out for one frame size and zoom.
    func probe(frameWidth: Int, zoom: CGFloat) -> Probe {
        var linear: [Int] = []
        linear.reserveCapacity(offsets.count)
        var reach = (left: 0, right: 0, up: 0, down: 0)
        for offset in offsets {
            let dx = Int((CGFloat(offset.x) * zoom).rounded())
            let dy = Int((CGFloat(offset.y) * zoom).rounded())
            linear.append(dy * frameWidth + dx)
            reach = (
                left: max(reach.left, -dx),
                right: max(reach.right, dx),
                up: max(reach.up, -dy),
                down: max(reach.down, dy)
            )
        }
        return Probe(linear: linear, values: values, reach: reach)
    }

    struct Probe {
        let linear: [Int]
        let values: [Float]
        let reach: (left: Int, right: Int, up: Int, down: Int)

        /// Normalized cross-correlation with the patch centered on pixel (x, y).
        /// Nil when the patch would leave the frame.
        func correlation(in frame: LiveTranslateGrayFrame, x: Int, y: Int) -> Float? {
            guard x >= reach.left, x + reach.right < frame.width,
                  y >= reach.up, y + reach.down < frame.height
            else { return nil }
            let base = y * frame.width + x
            var sum: Float = 0
            var sumOfSquares: Float = 0
            var dot: Float = 0
            frame.pixels.withUnsafeBufferPointer { pixels in
                linear.withUnsafeBufferPointer { linear in
                    values.withUnsafeBufferPointer { values in
                        for index in 0..<linear.count {
                            let value = Float(pixels[base + linear[index]])
                            sum += value
                            sumOfSquares += value * value
                            dot += values[index] * value
                        }
                    }
                }
            }
            let count = Float(linear.count)
            let spread = sumOfSquares - sum * sum / count
            guard spread > count else { return 0 }
            return dot / spread.squareRoot()
        }

        /// The best-correlated pixel within `radius` of `center`.
        func bestMatch(
            in frame: LiveTranslateGrayFrame,
            around center: (x: Int, y: Int),
            radius: Int
        ) -> (x: Int, y: Int, score: Float)? {
            var best: (x: Int, y: Int, score: Float)?
            for y in (center.y - radius)...(center.y + radius) {
                for x in (center.x - radius)...(center.x + radius) {
                    guard let score = correlation(in: frame, x: x, y: y) else { continue }
                    if best.map({ score > $0.score }) ?? true {
                        best = (x: x, y: y, score: score)
                    }
                }
            }
            return best
        }
    }
}

/// Moves each overlay with its text on every camera frame between OCR passes.
///
/// Each OCR pass anchors every overlay to a patch of the frame that pass read.
/// On each later frame, the follower looks for every patch near where it last
/// was, first on a half-size copy of the frame and then at full size. From the
/// patches it finds, it fits the camera's pan and zoom since the anchored
/// frame. That fit sizes every overlay and moves the ones whose patch is lost
/// to blur, glare, or the frame edge.
///
/// OCR takes several frames, so an anchored frame is already old when its
/// results arrive. The follower keeps the motion of each frame since, and
/// starts each new patch's search where that motion puts it. When shake blurred
/// the frame OCR read, its patches would match a few pixels off, so the
/// follower keeps following the sharper patches it has.
struct LiveTranslateFollower {
    /// Search reach per frame, in full-size pixels.
    static let searchRadius = 24
    /// Reach when the motion since the anchored frame is unknown.
    static let wideSearchRadius = 64
    /// Correlation a full-size match needs.
    static let minimumScore: Float = 0.5
    /// Correlation a half-size match needs before refining it.
    static let minimumCoarseScore: Float = 0.35
    /// Frames of motion kept for OCR results that arrive late.
    static let logLength = 120
    /// A new patch this much less sharp than the one it would replace is blurred.
    static let blurRatio: Float = 0.75
    /// Blurred OCR frames skipped in a row before re-anchoring anyway.
    static let maximumSkippedRebases = 3

    private struct Anchor {
        let fine: LiveTranslatePatch?
        let coarse: LiveTranslatePatch?
        /// Center in the anchored frame, in full-size pixels.
        let origin: CGPoint
        /// Overlay size in the anchored frame.
        let size: CGSize
        /// `origin` minus the pixel the patches are centered on.
        let offset: CGPoint
        /// Center in the latest frame.
        var center: CGPoint
    }

    private struct Frame {
        let number: Int
        let fine: LiveTranslateGrayFrame
        let coarse: LiveTranslateGrayFrame
    }

    /// Motion from the anchored frame to frame `number`, and whether any patch
    /// was found to measure it.
    private struct Step {
        let number: Int
        let motion: LiveTranslateMotion
        let measured: Bool
    }

    private var anchors: [String: Anchor] = [:]
    /// Camera motion from the anchored frame to the latest frame.
    private var motion = LiveTranslateMotion.identity
    private var log: [Step] = []
    private var held: [Int: LiveTranslateGrayFrame] = [:]
    private var latest: Frame?
    private var skippedRebases = 0

    /// Vision-normalized overlay boxes (origin bottom-left) in the latest frame, by track id.
    var positions: [String: CGRect] {
        guard let latest else { return [:] }
        let width = CGFloat(latest.fine.width)
        let height = CGFloat(latest.fine.height)
        return anchors.mapValues { anchor in
            let size = CGSize(width: anchor.size.width * motion.scale, height: anchor.size.height * motion.scale)
            return CGRect(
                x: (anchor.center.x - size.width / 2) / width,
                y: 1 - (anchor.center.y + size.height / 2) / height,
                width: size.width / width,
                height: size.height / height
            )
        }
    }

    mutating func reset() {
        anchors = [:]
        motion = .identity
        log = []
        held = [:]
        skippedRebases = 0
    }

    /// Keeps frame `number` until its OCR result comes back to `rebase`.
    mutating func hold(_ frame: LiveTranslateGrayFrame, for number: Int) {
        held[number] = frame
        while held.count > 2, let oldest = held.keys.min() {
            held.removeValue(forKey: oldest)
        }
    }

    /// Finds every anchored patch in the next camera frame.
    mutating func advance(to frame: LiveTranslateGrayFrame, number: Int) {
        let next = Frame(number: number, fine: frame, coarse: frame.halved())
        if let latest, latest.fine.width != frame.width || latest.fine.height != frame.height {
            reset()
        }
        latest = next
        var found: [String: CGPoint] = [:]
        for (id, anchor) in anchors {
            if let center = Self.locate(anchor, in: next, near: anchor.center, zoom: motion.scale, radius: Self.searchRadius) {
                found[id] = center
            }
        }
        settle(found: found, fallback: motion)
        record(number, measured: !found.isEmpty)
    }

    /// Re-anchors to the overlays OCR produced for frame `number`, given as
    /// Vision-normalized boxes by track id.
    mutating func rebase(_ boxes: [String: CGRect], from number: Int) {
        guard let source = held.removeValue(forKey: number), let latest,
              source.width == latest.fine.width, source.height == latest.fine.height
        else {
            anchors = [:]
            return
        }
        held = held.filter { $0.key > number }
        if isBlurrierThanAnchors(source, boxes: boxes), skippedRebases < Self.maximumSkippedRebases {
            skippedRebases += 1
            anchors = anchors.filter { boxes[$0.key] != nil }
            return
        }
        skippedRebases = 0

        // Re-express the log from the new anchored frame.
        var predicted = LiveTranslateMotion.identity
        var measured = false
        if let start = log.first(where: { $0.number == number }) {
            let undo = start.motion.inverted()
            log = log.filter { $0.number >= number }.map { step in
                Step(
                    number: step.number,
                    motion: undo.then(step.motion),
                    measured: step.number == number || step.measured
                )
            }
            predicted = log.last?.motion ?? .identity
            measured = log.allSatisfy(\.measured)
        } else {
            log = []
        }

        let sourceCoarse = source.halved()
        let width = CGFloat(source.width)
        let height = CGFloat(source.height)
        let radius = measured ? Self.searchRadius : Self.wideSearchRadius
        var fresh: [String: Anchor] = [:]
        var found: [String: CGPoint] = [:]
        for (id, box) in boxes {
            let origin = CGPoint(x: box.midX * width, y: (1 - box.midY) * height)
            let size = CGSize(width: box.width * width, height: box.height * height)
            let pixel = (x: Int(origin.x.rounded()), y: Int(origin.y.rounded()))
            let anchor = Anchor(
                fine: LiveTranslatePatch(frame: source, center: pixel, size: size),
                coarse: LiveTranslatePatch(
                    frame: sourceCoarse,
                    center: (Int((origin.x / 2).rounded()), Int((origin.y / 2).rounded())),
                    size: CGSize(width: size.width / 2, height: size.height / 2)
                ),
                origin: origin,
                size: size,
                offset: CGPoint(x: origin.x - CGFloat(pixel.x), y: origin.y - CGFloat(pixel.y)),
                center: predicted.apply(to: origin)
            )
            fresh[id] = anchor
            if let center = Self.locate(anchor, in: latest, near: anchor.center, zoom: predicted.scale, radius: radius) {
                found[id] = center
            }
        }
        anchors = fresh
        settle(found: found, fallback: predicted)
        if !log.isEmpty {
            log.removeLast()
        }
        record(latest.number, measured: measured || !found.isEmpty)
    }

    /// Whether most lines already followed look blurrier in `source` than in
    /// the patches the follower has.
    private func isBlurrierThanAnchors(_ source: LiveTranslateGrayFrame, boxes: [String: CGRect]) -> Bool {
        var compared = 0
        var blurrier = 0
        for (id, box) in boxes {
            guard let current = anchors[id]?.fine else { continue }
            let width = CGFloat(source.width)
            let height = CGFloat(source.height)
            guard let candidate = LiveTranslatePatch(
                frame: source,
                center: (Int((box.midX * width).rounded()), Int(((1 - box.midY) * height).rounded())),
                size: CGSize(width: box.width * width, height: box.height * height)
            ) else { continue }
            compared += 1
            if candidate.sharpness < current.sharpness * Self.blurRatio {
                blurrier += 1
            }
        }
        return compared > 0 && blurrier * 2 > compared
    }

    /// Fits the motion to the patches found, drops matches that disagree with
    /// it, and places every overlay.
    private mutating func settle(found: [String: CGPoint], fallback: LiveTranslateMotion) {
        var inliers = found
        var fitted = fallback
        for _ in 0..<3 {
            let pairs = inliers.compactMap { id, center in anchors[id].map { (from: $0.origin, to: center) } }
            guard !pairs.isEmpty else {
                fitted = fallback
                break
            }
            fitted = LiveTranslateMotion.fit(pairs, minimumSpan: 12, scaleRange: 0.5...2, fallbackScale: fallback.scale)
            let kept = inliers.filter { id, center in
                guard let anchor = anchors[id] else { return false }
                let expected = fitted.apply(to: anchor.origin)
                let tolerance = max(4, anchor.size.height * fitted.scale * 0.6)
                return hypot(center.x - expected.x, center.y - expected.y) <= tolerance
            }
            if kept.count == inliers.count { break }
            inliers = kept
        }
        motion = fitted
        for id in anchors.keys {
            guard let anchor = anchors[id] else { continue }
            anchors[id]?.center = inliers[id] ?? fitted.apply(to: anchor.origin)
        }
    }

    private mutating func record(_ number: Int, measured: Bool) {
        log.append(Step(number: number, motion: motion, measured: measured))
        if log.count > Self.logLength {
            log.removeFirst(log.count - Self.logLength)
        }
    }

    /// Where `anchor`'s patch sits in `frame`, searching within `radius`
    /// full-size pixels of `guess`, or nil when it isn't there.
    private static func locate(
        _ anchor: Anchor,
        in frame: Frame,
        near guess: CGPoint,
        zoom: CGFloat,
        radius: Int
    ) -> CGPoint? {
        guard let coarse = anchor.coarse, let fine = anchor.fine else { return nil }
        let shift = CGPoint(x: anchor.offset.x * zoom, y: anchor.offset.y * zoom)
        let coarseProbe = coarse.probe(frameWidth: frame.coarse.width, zoom: zoom)
        guard let rough = coarseProbe.bestMatch(
            in: frame.coarse,
            around: (Int(((guess.x - shift.x) / 2).rounded()), Int(((guess.y - shift.y) / 2).rounded())),
            radius: max(1, radius / 2)
        ), rough.score >= minimumCoarseScore else { return nil }

        let fineProbe = fine.probe(frameWidth: frame.fine.width, zoom: zoom)
        guard let best = fineProbe.bestMatch(in: frame.fine, around: (rough.x * 2, rough.y * 2), radius: 2),
              best.score >= minimumScore
        else { return nil }

        func vertex(_ before: Float?, _ after: Float?) -> CGFloat {
            guard let before, let after else { return 0 }
            let curvature = before - 2 * best.score + after
            guard curvature < 0 else { return 0 }
            return CGFloat(min(max((before - after) / (2 * curvature), -0.5), 0.5))
        }
        let dx = vertex(
            fineProbe.correlation(in: frame.fine, x: best.x - 1, y: best.y),
            fineProbe.correlation(in: frame.fine, x: best.x + 1, y: best.y)
        )
        let dy = vertex(
            fineProbe.correlation(in: frame.fine, x: best.x, y: best.y - 1),
            fineProbe.correlation(in: frame.fine, x: best.x, y: best.y + 1)
        )
        return CGPoint(x: CGFloat(best.x) + dx + shift.x, y: CGFloat(best.y) + dy + shift.y)
    }
}

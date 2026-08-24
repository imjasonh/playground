import ImageIO
import UniformTypeIdentifiers
import UIKit

/// Builds an animated GIF of captured doom faces in the status-bar idle order.
enum DoomFaceGIFExporter {
    static let defaultFrameDelay: Double = 0.22
    static let defaultMaxDimension: CGFloat = 240

    /// Idle look cycle used by Doom’s status bar: left → center → right → center.
    static func idleLookSequence(health: Int) -> [DoomFaceSlot] {
        let expressions: [DoomFaceExpression] = [.lookLeft, .lookCenter, .lookRight, .lookCenter]
        return expressions.map { DoomFaceSlot(health: health, expression: $0) }
    }

    /// Picks frames for export: prefer a full look-cycle on the best health row,
    /// otherwise every captured face in sheet order.
    static func frames(
        from captures: [DoomFaceSlot: UIImage]
    ) -> [UIImage] {
        guard !captures.isEmpty else { return [] }

        var bestHealth: Int?
        var bestCount = -1
        for health in 0..<DoomFaceSheetLayout.healthRowCount {
            let count = [DoomFaceExpression.lookLeft, .lookCenter, .lookRight]
                .filter { captures[DoomFaceSlot(health: health, expression: $0)] != nil }
                .count
            if count > bestCount {
                bestCount = count
                bestHealth = health
            }
        }

        if let health = bestHealth, bestCount >= 2 {
            let sequence = idleLookSequence(health: health).compactMap { captures[$0] }
            if sequence.count >= 2 {
                return sequence
            }
        }

        return DoomFaceSheetLayout.allSlots.compactMap { captures[$0] }
    }

    static func makeGIF(
        captures: [DoomFaceSlot: UIImage],
        frameDelay: Double = defaultFrameDelay,
        maxDimension: CGFloat = defaultMaxDimension
    ) -> Data? {
        let images = frames(from: captures)
        guard images.count >= 2 else { return nil }
        return encode(frames: images, frameDelay: frameDelay, maxDimension: maxDimension)
    }

    static func writeTemporaryGIF(
        captures: [DoomFaceSlot: UIImage],
        frameDelay: Double = defaultFrameDelay,
        maxDimension: CGFloat = defaultMaxDimension
    ) throws -> URL {
        guard let data = makeGIF(
            captures: captures,
            frameDelay: frameDelay,
            maxDimension: maxDimension
        ) else {
            throw ExportError.notEnoughFaces
        }
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("doomface-\(UUID().uuidString)")
            .appendingPathExtension("gif")
        try data.write(to: url, options: .atomic)
        return url
    }

    static func encode(
        frames: [UIImage],
        frameDelay: Double,
        maxDimension: CGFloat
    ) -> Data? {
        guard frames.count >= 2 else { return nil }
        let delay = max(frameDelay, 0.05)
        let prepared: [CGImage] = frames.compactMap { scaledCGImage(from: $0, maxDimension: maxDimension) }
        guard prepared.count == frames.count else { return nil }

        let data = NSMutableData()
        guard let destination = CGImageDestinationCreateWithData(
            data,
            UTType.gif.identifier as CFString,
            prepared.count,
            nil
        ) else {
            return nil
        }

        let fileProperties: [CFString: Any] = [
            kCGImagePropertyGIFDictionary: [
                kCGImagePropertyGIFLoopCount: 0,
            ],
        ]
        CGImageDestinationSetProperties(destination, fileProperties as CFDictionary)

        let frameProperties: [CFString: Any] = [
            kCGImagePropertyGIFDictionary: [
                kCGImagePropertyGIFDelayTime: delay,
                kCGImagePropertyGIFUnclampedDelayTime: delay,
            ],
        ]

        for frame in prepared {
            CGImageDestinationAddImage(destination, frame, frameProperties as CFDictionary)
        }

        guard CGImageDestinationFinalize(destination) else { return nil }
        return data as Data
    }

    private static func scaledCGImage(from image: UIImage, maxDimension: CGFloat) -> CGImage? {
        guard let cgImage = image.cgImage else { return nil }
        let width = CGFloat(cgImage.width)
        let height = CGFloat(cgImage.height)
        guard width > 0, height > 0 else { return nil }

        let longest = max(width, height)
        let scale = longest > maxDimension ? (maxDimension / longest) : 1
        let target = CGSize(
            width: max(1, (width * scale).rounded()),
            height: max(1, (height * scale).rounded())
        )

        if scale == 1, image.imageOrientation == .up {
            return cgImage
        }

        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        let rendered = UIGraphicsImageRenderer(size: target, format: format).image { _ in
            image.draw(in: CGRect(origin: .zero, size: target))
        }
        return rendered.cgImage
    }

    enum ExportError: LocalizedError {
        case notEnoughFaces

        var errorDescription: String? {
            "Capture at least two faces before exporting a GIF."
        }
    }
}

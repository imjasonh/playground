import ImageIO
import UniformTypeIdentifiers
import UIKit

/// Builds an animated GIF that alternates stereo eye frames (a wigglegram).
enum WiggleGIFEncoder {
    /// Default per-frame delay — matches `WigglegramView.halfPeriod` on main.
    static let defaultFrameDelay: Double = 0.22
    /// Cap the long edge so shareable GIFs stay reasonably small.
    static let defaultMaxDimension: CGFloat = 720

    /// Encode `left`/`right` as a looping two-frame GIF.
    static func makeWiggleGIF(
        left: UIImage,
        right: UIImage,
        frameDelay: Double = defaultFrameDelay,
        maxDimension: CGFloat = defaultMaxDimension
    ) -> Data? {
        makeGIFData(
            frames: [left, right],
            frameDelay: frameDelay,
            maxDimension: maxDimension
        )
    }

    static func makeGIFData(
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

    /// Writes a wiggle GIF to a unique temp file for the system share sheet.
    static func writeTemporaryWiggleGIF(
        left: UIImage,
        right: UIImage,
        frameDelay: Double = defaultFrameDelay,
        maxDimension: CGFloat = defaultMaxDimension
    ) throws -> URL {
        guard let data = makeWiggleGIF(
            left: left,
            right: right,
            frameDelay: frameDelay,
            maxDimension: maxDimension
        ) else {
            throw EncoderError.encodingFailed
        }
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("viewmaster-wiggle-\(UUID().uuidString)")
            .appendingPathExtension("gif")
        try data.write(to: url, options: .atomic)
        return url
    }

    // MARK: - Scaling

    static func scaledCGImage(from image: UIImage, maxDimension: CGFloat) -> CGImage? {
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

    enum EncoderError: LocalizedError {
        case encodingFailed

        var errorDescription: String? {
            "Could not encode the wiggle GIF."
        }
    }
}

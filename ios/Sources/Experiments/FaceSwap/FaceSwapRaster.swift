import CoreGraphics
import Foundation
import UIKit

/// Straight RGBA8 buffer, origin top-left. Alpha is always 255.
///
/// Edits copy this buffer and write only destination-mask pixels. Comparing
/// two buffers is a byte check, which is what the diff view reports.
struct FaceSwapRaster: Equatable, Sendable {
    let width: Int
    let height: Int
    var rgba: [UInt8]

    var pixelCount: Int { width * height }

    init(width: Int, height: Int, rgba: [UInt8]) {
        self.width = width
        self.height = height
        self.rgba = rgba
    }

    static func solid(width: Int, height: Int, red: UInt8, green: UInt8, blue: UInt8) -> FaceSwapRaster {
        let count = max(0, width) * max(0, height)
        var rgba = [UInt8](repeating: 255, count: count * 4)
        var index = 0
        while index < rgba.count {
            rgba[index] = red
            rgba[index + 1] = green
            rgba[index + 2] = blue
            index += 4
        }
        return FaceSwapRaster(width: max(0, width), height: max(0, height), rgba: rgba)
    }

    func copy() -> FaceSwapRaster {
        FaceSwapRaster(width: width, height: height, rgba: rgba)
    }

    func index(x: Int, y: Int) -> Int? {
        guard x >= 0, y >= 0, x < width, y < height else { return nil }
        return (y * width + x) * 4
    }

    func rgb(x: Int, y: Int) -> (UInt8, UInt8, UInt8)? {
        guard let offset = index(x: x, y: y) else { return nil }
        return (rgba[offset], rgba[offset + 1], rgba[offset + 2])
    }

    mutating func setRGB(x: Int, y: Int, red: UInt8, green: UInt8, blue: UInt8) {
        guard let offset = index(x: x, y: y) else { return }
        rgba[offset] = red
        rgba[offset + 1] = green
        rgba[offset + 2] = blue
        rgba[offset + 3] = 255
    }

    /// Fills `rect` in pixel space, clipped to the buffer. Used by tests and cue sampling.
    mutating func fill(rect: CGRect, red: UInt8, green: UInt8, blue: UInt8) {
        let minX = max(0, Int(rect.minX.rounded(.down)))
        let maxX = min(width, Int(rect.maxX.rounded(.up)))
        let minY = max(0, Int(rect.minY.rounded(.down)))
        let maxY = min(height, Int(rect.maxY.rounded(.up)))
        guard minX < maxX, minY < maxY else { return }
        for y in minY..<maxY {
            for x in minX..<maxX {
                setRGB(x: x, y: y, red: red, green: green, blue: blue)
            }
        }
    }

    func meanLuma(in rect: CGRect) -> (luma: Double, count: Int) {
        let minX = max(0, Int(rect.minX.rounded(.down)))
        let maxX = min(width, Int(rect.maxX.rounded(.up)))
        let minY = max(0, Int(rect.minY.rounded(.down)))
        let maxY = min(height, Int(rect.maxY.rounded(.up)))
        guard minX < maxX, minY < maxY else { return (0, 0) }
        var sum = 0.0
        var count = 0
        for y in minY..<maxY {
            for x in minX..<maxX {
                guard let color = rgb(x: x, y: y) else { continue }
                sum += 0.2126 * Double(color.0) + 0.7152 * Double(color.1) + 0.0722 * Double(color.2)
                count += 1
            }
        }
        guard count > 0 else { return (0, 0) }
        return (sum / Double(count), count)
    }

    func makeCGImage() -> CGImage? {
        guard width > 0, height > 0, rgba.count == width * height * 4 else { return nil }
        let data = Data(rgba)
        guard let provider = CGDataProvider(data: data as CFData) else { return nil }
        return CGImage(
            width: width,
            height: height,
            bitsPerComponent: 8,
            bitsPerPixel: 32,
            bytesPerRow: width * 4,
            space: CGColorSpaceCreateDeviceRGB(),
            bitmapInfo: CGBitmapInfo(rawValue: CGImageAlphaInfo.premultipliedLast.rawValue),
            provider: provider,
            decode: nil,
            shouldInterpolate: false,
            intent: .defaultIntent
        )
    }

    func uiImage() -> UIImage? {
        guard let cgImage = makeCGImage() else { return nil }
        return UIImage(cgImage: cgImage, scale: 1, orientation: .up)
    }

    /// Bakes orientation and scales so the long edge is at most `maxEdge`.
    static func decode(_ image: UIImage, maxEdge: Int) -> (raster: FaceSwapRaster, wasScaled: Bool)? {
        guard let cgImage = orientedCGImage(from: image, maxEdge: maxEdge) else { return nil }
        guard let raster = read(cgImage) else { return nil }
        let sourceLong = max(image.size.width * image.scale, image.size.height * image.scale)
        let wasScaled = sourceLong > CGFloat(maxEdge) + 0.5
        return (raster, wasScaled)
    }

    static func read(_ cgImage: CGImage) -> FaceSwapRaster? {
        let width = cgImage.width
        let height = cgImage.height
        guard width > 0, height > 0 else { return nil }
        var rgba = [UInt8](repeating: 0, count: width * height * 4)
        let wrote = rgba.withUnsafeMutableBytes { raw -> Bool in
            guard let base = raw.baseAddress else { return false }
            guard let context = CGContext(
                data: base,
                width: width,
                height: height,
                bitsPerComponent: 8,
                bytesPerRow: width * 4,
                space: CGColorSpaceCreateDeviceRGB(),
                bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
            ) else {
                return false
            }
            context.interpolationQuality = .high
            context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))
            return true
        }
        guard wrote else { return nil }
        var index = 3
        while index < rgba.count {
            rgba[index] = 255
            index += 4
        }
        return FaceSwapRaster(width: width, height: height, rgba: rgba)
    }

    private static func orientedCGImage(from image: UIImage, maxEdge: Int) -> CGImage? {
        let pixelWidth = image.size.width * image.scale
        let pixelHeight = image.size.height * image.scale
        guard pixelWidth > 0, pixelHeight > 0 else { return nil }
        let longest = max(pixelWidth, pixelHeight)
        let cap = CGFloat(max(1, maxEdge))
        let scale = longest > cap ? cap / longest : 1
        let target = CGSize(
            width: max(1, (pixelWidth * scale).rounded()),
            height: max(1, (pixelHeight * scale).rounded())
        )
        if scale == 1, image.imageOrientation == .up, let cgImage = image.cgImage,
           cgImage.width == Int(target.width), cgImage.height == Int(target.height)
        {
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
}

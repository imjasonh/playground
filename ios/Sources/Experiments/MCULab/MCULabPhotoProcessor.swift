import CoreGraphics
import Foundation
#if canImport(UIKit)
import UIKit
#endif

/// Display pixel mode for the Waveshare 7.5″ V2 (UC8179) photo frame.
/// Mirrors `PhotoMode` in `mcu-lab/src/photo.rs`.
enum MCULabPhotoMode: UInt8, CaseIterable, Identifiable, Sendable {
    case gray4 = 1
    case bw1Bit = 0

    var id: UInt8 { rawValue }

    var displayName: String {
        switch self {
        case .gray4: return "4-Gray (2-bit)"
        case .bw1Bit: return "1-Bit B&W"
        }
    }

    var frameBytes: Int {
        switch self {
        case .bw1Bit: return MCULabPhotoProcessor.bwFrameBytes
        case .gray4: return MCULabPhotoProcessor.gray4FrameBytes
        }
    }

    var maxPhotos: Int {
        (Int(MCULabProtocol.otaSlotBytes) - MCULabPhotoProcessor.headerLength) / frameBytes
    }
}

/// Serpentine error-diffusion dithering kernel.
enum MCULabPhotoDitherAlgorithm: String, CaseIterable, Identifiable, Sendable {
    case jarvisJudiceNinke = "jjn"
    case floydSteinberg = "floyd-steinberg"
    case atkinson = "atkinson"
    case stucki = "stucki"

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .jarvisJudiceNinke: return "Jarvis-Judice-Ninke"
        case .floydSteinberg: return "Floyd-Steinberg"
        case .atkinson: return "Atkinson"
        case .stucki: return "Stucki"
        }
    }
}

/// How source photos are framed into the 800×480 landscape panel.
enum MCULabPhotoFitMode: String, CaseIterable, Identifiable, Sendable {
    case fill = "fill"
    case fitWhite = "fit-white"
    case fitBlack = "fit-black"

    var id: String { rawValue }

    var displayName: String {
        switch self {
        case .fill: return "Fill (Crop)"
        case .fitWhite: return "Fit (White Matte)"
        case .fitBlack: return "Fit (Black Matte)"
        }
    }
}

/// Configurable quantization, tone-mapping, and dithering options.
struct MCULabPhotoOptions: Equatable, Sendable {
    var mode: MCULabPhotoMode = .gray4
    var dither: MCULabPhotoDitherAlgorithm = .jarvisJudiceNinke
    var fit: MCULabPhotoFitMode = .fill
    var rotatePortrait: Bool = false
    var autoContrast: Bool = true
    var sharpenAmount: Double = 0.35
    var gamma: Double = 1.0
}

/// Parsed 20-byte `MCUP` photo album header. Mirrors `PhotoAlbumHeader` in `mcu-lab/src/photo.rs`.
struct MCULabPhotoAlbumHeader: Equatable, Sendable {
    let mode: MCULabPhotoMode
    let count: UInt16
    let intervalSecs: UInt32
    let payloadCRC32: UInt32
}

/// Result of processing a single photo for the Waveshare 7.5″ 800×480 display.
struct MCULabProcessedPhoto: Sendable {
    /// Packed frame bytes ready for the `MCUP` album (48,000 B for B&W, 96,000 B for 4-gray).
    let frameData: Data
    /// Quantized pixel levels (`0 = black, 1 = dark gray, 2 = light gray, 3 = white`), length 384,000.
    let levels: [UInt8]
}

/// High-quality linear-light tone mapper, unsharp sharpener, serpentine error-diffusion
/// ditherer, and `MCUP` album encoder for the Waveshare 7.5″ 800×480 (UC8179) display.
enum MCULabPhotoProcessor {
    static let panelWidth = 800
    static let panelHeight = 480
    static let pixelCount = panelWidth * panelHeight
    static let bwFrameBytes = (panelWidth / 8) * panelHeight // 48,000
    static let gray4FrameBytes = bwFrameBytes * 2            // 96,000
    static let headerLength = 20
    static let magic: [UInt8] = [0x4D, 0x43, 0x55, 0x50]     // "MCUP"
    static let version: UInt8 = 1
    static let defaultRotateIntervalSecs: UInt32 = 600       // 10 minutes

    /// Linear-light reflectance levels approximating the physical UC8179 4-gray LUT.
    private static let gray4LinearPalette: [Float] = [0.0, 0.22, 0.56, 1.0]

    /// Precomputed sRGB byte (0..255) → linear light (0.0..1.0) lookup table.
    private static let srgbToLinearLUT: [Float] = (0..<256).map { i in
        let v = Float(i) / 255.0
        if v <= 0.04045 {
            return v / 12.92
        }
        return powf((v + 0.055) / 1.055, 2.4)
    }

    #if canImport(UIKit)
    /// Normalize a `UIImage`'s EXIF orientation into an upright `CGImage`.
    static func uprightCGImage(from image: UIImage) -> CGImage? {
        if image.imageOrientation == .up, let cg = image.cgImage {
            return cg
        }
        let size = image.size
        guard size.width > 0, size.height > 0 else { return image.cgImage }
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1.0
        format.opaque = true
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        let normalized = renderer.image { _ in
            image.draw(in: CGRect(origin: .zero, size: size))
        }
        return normalized.cgImage
    }
    #endif

    /// Process a `CGImage` into a packed Waveshare 7.5″ frame and previewable 4-level map.
    static func process(
        cgImage: CGImage,
        options: MCULabPhotoOptions = MCULabPhotoOptions()
    ) -> MCULabProcessedPhoto? {
        let shouldRotate = options.rotatePortrait && cgImage.height > cgImage.width
        guard let rgba = renderToPanelRGBA(
            cgImage: cgImage,
            fit: options.fit,
            rotate90: shouldRotate
        ) else {
            return nil
        }
        var lum = linearLuminance(fromRGBA: rgba)
        if options.autoContrast {
            applyAutoContrast(&lum)
        }
        if options.sharpenAmount > 0.001 {
            lum = applyUnsharpMask(
                lum,
                width: panelWidth,
                height: panelHeight,
                amount: Float(options.sharpenAmount)
            )
        }
        if abs(options.gamma - 1.0) > 0.001 {
            applyGamma(&lum, gamma: Float(options.gamma))
        }
        let levels = dither(
            linearLuminance: lum,
            width: panelWidth,
            height: panelHeight,
            mode: options.mode,
            algorithm: options.dither
        )
        let frameData: Data
        switch options.mode {
        case .bw1Bit:
            frameData = packBW1Bit(levels: levels)
        case .gray4:
            frameData = packGray4Planes(levels: levels)
        }
        return MCULabProcessedPhoto(frameData: frameData, levels: levels)
    }

    /// Render a `CGImage` to an 800×480 sRGB RGBA buffer using high-quality resampling.
    static func renderToPanelRGBA(
        cgImage: CGImage,
        fit: MCULabPhotoFitMode,
        rotate90: Bool
    ) -> [UInt8]? {
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        var rgba = [UInt8](repeating: 255, count: pixelCount * 4)
        let bitmapInfo = CGImageAlphaInfo.premultipliedLast.rawValue
        guard let ctx = CGContext(
            data: &rgba,
            width: panelWidth,
            height: panelHeight,
            bitsPerComponent: 8,
            bytesPerRow: panelWidth * 4,
            space: colorSpace,
            bitmapInfo: bitmapInfo
        ) else {
            return nil
        }

        ctx.interpolationQuality = .high
        ctx.setShouldAntialias(true)

        // Fill background matte.
        if fit == .fitBlack {
            ctx.setFillColor(red: 0, green: 0, blue: 0, alpha: 1)
        } else {
            ctx.setFillColor(red: 1, green: 1, blue: 1, alpha: 1)
        }
        ctx.fill(CGRect(x: 0, y: 0, width: panelWidth, height: panelHeight))

        let srcW = CGFloat(rotate90 ? cgImage.height : cgImage.width)
        let srcH = CGFloat(rotate90 ? cgImage.width : cgImage.height)
        guard srcW > 0, srcH > 0 else { return nil }

        let dstW = CGFloat(panelWidth)
        let dstH = CGFloat(panelHeight)
        let scale: CGFloat = switch fit {
        case .fill:
            max(dstW / srcW, dstH / srcH)
        case .fitWhite, .fitBlack:
            min(dstW / srcW, dstH / srcH)
        }

        let drawW = srcW * scale
        let drawH = srcH * scale

        ctx.saveGState()
        ctx.translateBy(x: dstW / 2.0, y: dstH / 2.0)
        if rotate90 {
            ctx.rotate(by: -.pi / 2.0)
            ctx.draw(
                cgImage,
                in: CGRect(x: -drawH / 2.0, y: -drawW / 2.0, width: drawH, height: drawW)
            )
        } else {
            ctx.draw(
                cgImage,
                in: CGRect(x: -drawW / 2.0, y: -drawH / 2.0, width: drawW, height: drawH)
            )
        }
        ctx.restoreGState()
        return rgba
    }

    /// Convert sRGB RGBA bytes into linear-light Rec. 709 luminance `[0.0, 1.0]`.
    static func linearLuminance(fromRGBA rgba: [UInt8]) -> [Float] {
        let count = rgba.count / 4
        var out = [Float](repeating: 0, count: count)
        let lut = srgbToLinearLUT
        for i in 0..<count {
            let base = i * 4
            let r = lut[Int(rgba[base])]
            let g = lut[Int(rgba[base + 1])]
            let b = lut[Int(rgba[base + 2])]
            out[i] = 0.2126 * r + 0.7152 * g + 0.0722 * b
        }
        return out
    }

    /// Stretch luminance using 1%–99% percentiles so e-paper uses its full tonal range
    /// without letting isolated specular pixels crush midtones.
    static func applyAutoContrast(_ lum: inout [Float]) {
        let bins = 1024
        var hist = [Int](repeating: 0, count: bins)
        for v in lum {
            let clamped = min(max(v, 0), 1)
            let idx = min(bins - 1, Int(clamped * Float(bins - 1)))
            hist[idx] += 1
        }
        let total = lum.count
        guard total > 0 else { return }
        let lowTarget = total / 100
        let highTarget = total - lowTarget

        var acc = 0
        var lowBin = 0
        for i in 0..<bins {
            acc += hist[i]
            if acc >= lowTarget {
                lowBin = i
                break
            }
        }
        acc = 0
        var highBin = bins - 1
        for i in 0..<bins {
            acc += hist[i]
            if acc >= highTarget {
                highBin = i
                break
            }
        }
        let lo = Float(lowBin) / Float(bins - 1)
        let hi = Float(highBin) / Float(bins - 1)
        let span = hi - lo
        guard span > 0.05 else { return }
        let invSpan = 1.0 / span
        for i in 0..<lum.count {
            lum[i] = min(max((lum[i] - lo) * invSpan, 0), 1)
        }
    }

    /// Separable 3×3 Gaussian unsharp mask in linear light to keep edges crisp on e-paper.
    static func applyUnsharpMask(
        _ lum: [Float],
        width: Int,
        height: Int,
        amount: Float
    ) -> [Float] {
        guard width >= 3, height >= 3, lum.count == width * height else { return lum }
        var horiz = [Float](repeating: 0, count: lum.count)
        for y in 0..<height {
            let row = y * width
            horiz[row] = (3 * lum[row] + lum[row + 1]) * 0.25
            for x in 1..<(width - 1) {
                horiz[row + x] = (lum[row + x - 1] + 2 * lum[row + x] + lum[row + x + 1]) * 0.25
            }
            horiz[row + width - 1] = (lum[row + width - 2] + 3 * lum[row + width - 1]) * 0.25
        }

        var out = [Float](repeating: 0, count: lum.count)
        for y in 0..<height {
            let ym1 = max(0, y - 1) * width
            let y0 = y * width
            let yp1 = min(height - 1, y + 1) * width
            for x in 0..<width {
                let blur = (horiz[ym1 + x] + 2 * horiz[y0 + x] + horiz[yp1 + x]) * 0.25
                let orig = lum[y0 + x]
                out[y0 + x] = min(max(orig + amount * (orig - blur), 0), 1)
            }
        }
        return out
    }

    /// Apply midtone gamma curve in linear light.
    static func applyGamma(_ lum: inout [Float], gamma: Float) {
        for i in 0..<lum.count {
            let v = min(max(lum[i], 0), 1)
            lum[i] = powf(v, gamma)
        }
    }

    /// Serpentine error-diffusion dithering in linear light.
    /// Returns pixel levels in `0...3` (`0 = black, 1 = dark gray, 2 = light gray, 3 = white`).
    /// In `.bw1Bit` mode, only levels `0` and `3` are emitted.
    static func dither(
        linearLuminance: [Float],
        width: Int,
        height: Int,
        mode: MCULabPhotoMode,
        algorithm: MCULabPhotoDitherAlgorithm
    ) -> [UInt8] {
        var buf = linearLuminance
        var levels = [UInt8](repeating: 3, count: width * height)

        // Kernel taps: (dx, dy, weight) where dx is along the current scan direction.
        let taps: [(Int, Int, Float)]
        switch algorithm {
        case .floydSteinberg:
            taps = [
                (1, 0, 7.0 / 16.0),
                (-1, 1, 3.0 / 16.0),
                (0, 1, 5.0 / 16.0),
                (1, 1, 1.0 / 16.0),
            ]
        case .atkinson:
            taps = [
                (1, 0, 1.0 / 8.0),
                (2, 0, 1.0 / 8.0),
                (-1, 1, 1.0 / 8.0),
                (0, 1, 1.0 / 8.0),
                (1, 1, 1.0 / 8.0),
                (0, 2, 1.0 / 8.0),
            ]
        case .jarvisJudiceNinke:
            taps = [
                (1, 0, 7.0 / 48.0),
                (2, 0, 5.0 / 48.0),
                (-2, 1, 3.0 / 48.0),
                (-1, 1, 5.0 / 48.0),
                (0, 1, 7.0 / 48.0),
                (1, 1, 5.0 / 48.0),
                (2, 1, 3.0 / 48.0),
                (-2, 2, 1.0 / 48.0),
                (-1, 2, 3.0 / 48.0),
                (0, 2, 5.0 / 48.0),
                (1, 2, 3.0 / 48.0),
                (2, 2, 1.0 / 48.0),
            ]
        case .stucki:
            taps = [
                (1, 0, 8.0 / 42.0),
                (2, 0, 4.0 / 42.0),
                (-2, 1, 2.0 / 42.0),
                (-1, 1, 4.0 / 42.0),
                (0, 1, 8.0 / 42.0),
                (1, 1, 4.0 / 42.0),
                (2, 1, 2.0 / 42.0),
                (-2, 2, 1.0 / 42.0),
                (-1, 2, 2.0 / 42.0),
                (0, 2, 4.0 / 42.0),
                (1, 2, 2.0 / 42.0),
                (2, 2, 1.0 / 42.0),
            ]
        }

        let palette = gray4LinearPalette
        for y in 0..<height {
            let reverse = (y & 1) == 1
            let rowStart = y * width
            let dir = reverse ? -1 : 1
            var x = reverse ? (width - 1) : 0
            for _ in 0..<width {
                let idx = rowStart + x
                let oldVal = min(max(buf[idx], 0), 1)
                let chosenLevel: UInt8
                let quantVal: Float
                switch mode {
                case .bw1Bit:
                    if oldVal >= 0.5 {
                        chosenLevel = 3
                        quantVal = 1.0
                    } else {
                        chosenLevel = 0
                        quantVal = 0.0
                    }
                case .gray4:
                    var bestIdx = 0
                    var bestDist = abs(oldVal - palette[0])
                    for p in 1..<4 {
                        let d = abs(oldVal - palette[p])
                        if d < bestDist {
                            bestDist = d
                            bestIdx = p
                        }
                    }
                    chosenLevel = UInt8(bestIdx)
                    quantVal = palette[bestIdx]
                }

                levels[idx] = chosenLevel
                let err = oldVal - quantVal
                for (dx, dy, weight) in taps {
                    let nx = x + dx * dir
                    let ny = y + dy
                    if nx >= 0, nx < width, ny < height {
                        buf[ny * width + nx] += err * weight
                    }
                }
                x += dir
            }
        }
        return levels
    }

    /// Pack 384,000 pixel levels (`0` or `3`) into a 48,000-byte 1-bit B&W buffer (MSB-first, 1 = white).
    static func packBW1Bit(levels: [UInt8]) -> Data {
        var bytes = [UInt8](repeating: 0, count: bwFrameBytes)
        for byteIdx in 0..<bwFrameBytes {
            let base = byteIdx * 8
            var acc: UInt8 = 0
            for bit in 0..<8 {
                if levels[base + bit] >= 2 {
                    acc |= 1 << (7 - bit)
                }
            }
            bytes[byteIdx] = acc
        }
        return Data(bytes)
    }

    /// Pack 384,000 pixel levels (`0..3`) into two contiguous 48,000-byte UC8179 bitplanes
    /// (`DTM1` + `DTM2` = 96,000 bytes), matching `pack_4gray_planes` in `mcu-lab/src/photo.rs`.
    static func packGray4Planes(levels: [UInt8]) -> Data {
        var out = [UInt8](repeating: 0, count: gray4FrameBytes)
        for byteIdx in 0..<bwFrameBytes {
            let base = byteIdx * 8
            var b1: UInt8 = 0
            var b2: UInt8 = 0
            for bit in 0..<8 {
                let lvl = levels[base + bit] & 0x03
                let shift = 7 - bit
                // 0 (black)      -> DTM1=1, DTM2=1
                // 1 (dark gray)  -> DTM1=0, DTM2=1
                // 2 (light gray) -> DTM1=1, DTM2=0
                // 3 (white)      -> DTM1=0, DTM2=0
                let p1: UInt8 = (lvl == 0 || lvl == 2) ? 1 : 0
                let p2: UInt8 = (lvl == 0 || lvl == 1) ? 1 : 0
                b1 |= p1 << shift
                b2 |= p2 << shift
            }
            out[byteIdx] = b1
            out[bwFrameBytes + byteIdx] = b2
        }
        return Data(out)
    }

    /// Build a realistic e-paper preview `CGImage` from quantized levels (`0..3`).
    static func makePreviewCGImage(levels: [UInt8]) -> CGImage? {
        guard levels.count == pixelCount else { return nil }
        // Approximate physical e-paper shades (matte off-black to paper off-white).
        let shadeLUT: [UInt8] = [22, 108, 182, 242]
        var gray = [UInt8](repeating: 242, count: pixelCount)
        for i in 0..<pixelCount {
            gray[i] = shadeLUT[Int(levels[i] & 0x03)]
        }
        let colorSpace = CGColorSpaceCreateDeviceGray()
        let data = Data(gray)
        guard let provider = CGDataProvider(data: data as CFData) else { return nil }
        return CGImage(
            width: panelWidth,
            height: panelHeight,
            bitsPerComponent: 8,
            bitsPerPixel: 8,
            bytesPerRow: panelWidth,
            space: colorSpace,
            bitmapInfo: CGBitmapInfo(rawValue: CGImageAlphaInfo.none.rawValue),
            provider: provider,
            decode: nil,
            shouldInterpolate: false,
            intent: .defaultIntent
        )
    }

    /// Encode a complete `MCUP` photo album binary matching `encode_photo_album` in `mcu-lab/src/photo.rs`.
    static func encodeAlbum(
        mode: MCULabPhotoMode,
        intervalSecs: UInt32,
        frames: [Data]
    ) -> Data? {
        guard !frames.isEmpty, frames.count <= mode.maxPhotos else { return nil }
        let expectedLen = mode.frameBytes
        var payload = Data(capacity: frames.count * expectedLen)
        for frame in frames {
            guard frame.count == expectedLen else { return nil }
            payload.append(frame)
        }
        let payloadCRC = MCULabProtocol.crc32(payload)
        var header = Data(capacity: headerLength)
        header.append(contentsOf: magic)
        header.append(version)
        header.append(mode.rawValue)
        appendLE(UInt16(frames.count), to: &header)
        appendLE(intervalSecs, to: &header)
        appendLE(payloadCRC, to: &header)
        let headerCRC = MCULabProtocol.crc32(header)
        appendLE(headerCRC, to: &header)

        var out = Data(capacity: headerLength + payload.count)
        out.append(header)
        out.append(payload)
        return out
    }

    /// Parse and validate a 20-byte `MCUP` header. Mirrors `PhotoAlbumHeader::parse` in `mcu-lab/src/photo.rs`.
    static func parseAlbumHeader(_ data: Data) -> MCULabPhotoAlbumHeader? {
        guard data.count >= headerLength else { return nil }
        let bytes = [UInt8](data.prefix(headerLength))
        guard Array(bytes[0..<4]) == magic, bytes[4] == version else { return nil }
        let expectedHdrCRC = readUInt32LE(bytes, at: 16)
        guard MCULabProtocol.crc32(Data(bytes[0..<16])) == expectedHdrCRC else { return nil }
        guard let mode = MCULabPhotoMode(rawValue: bytes[5]) else { return nil }
        let count = readUInt16LE(bytes, at: 6)
        guard count >= 1, Int(count) <= mode.maxPhotos else { return nil }
        let intervalSecs = readUInt32LE(bytes, at: 8)
        let payloadCRC = readUInt32LE(bytes, at: 12)
        return MCULabPhotoAlbumHeader(
            mode: mode,
            count: count,
            intervalSecs: intervalSecs,
            payloadCRC32: payloadCRC
        )
    }

    private static func appendLE(_ value: UInt16, to data: inout Data) {
        var le = value.littleEndian
        withUnsafeBytes(of: &le) { data.append(contentsOf: $0) }
    }

    private static func appendLE(_ value: UInt32, to data: inout Data) {
        var le = value.littleEndian
        withUnsafeBytes(of: &le) { data.append(contentsOf: $0) }
    }

    private static func readUInt16LE(_ bytes: [UInt8], at offset: Int) -> UInt16 {
        UInt16(bytes[offset]) | (UInt16(bytes[offset + 1]) << 8)
    }

    private static func readUInt32LE(_ bytes: [UInt8], at offset: Int) -> UInt32 {
        UInt32(bytes[offset])
            | (UInt32(bytes[offset + 1]) << 8)
            | (UInt32(bytes[offset + 2]) << 16)
            | (UInt32(bytes[offset + 3]) << 24)
    }
}

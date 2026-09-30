import CoreGraphics
import CoreImage

/// One pixel's color, channels in 0...1.
struct HairRGB: Equatable {
    var r: Float
    var g: Float
    var b: Float
}

/// Builds a hair mask by matching the crown color.
///
/// Apple's hair matte is a still-photo attachment. The live path has a person
/// matte and face landmarks, so a pixel is hair when it matches the color above
/// the face, differs from the cheeks and from the shirt, and connects back to
/// that crown. Bangs and long hair stay in. Skin below the eyebrows stays out.
enum HairAffinity {
    static let minimumSeparation: Float = 0.12
    static let hairMargin: Float = 0.05
    static let maxHairDistance: Float = 0.30
    static let personMinimum: UInt8 = 48
    static let minimumSampleCount = 4

    /// Grayscale mask, row 0 at the top. Empty when `colors` and `person` disagree in size.
    static func maskBytes(
        colors: [HairRGB],
        person: [UInt8],
        width: Int,
        height: Int,
        regions: [HairRegion]
    ) -> [UInt8] {
        let count = width * height
        guard width > 0, height > 0, colors.count == count, person.count == count else { return [] }
        var output = [UInt8](repeating: 0, count: count)
        for region in regions {
            let part = maskBytes(
                colors: colors,
                person: person,
                width: width,
                height: height,
                region: region
            )
            for index in output.indices where part[index] > output[index] {
                output[index] = part[index]
            }
        }
        return output
    }

    private static func maskBytes(
        colors: [HairRGB],
        person: [UInt8],
        width: Int,
        height: Int,
        region: HairRegion
    ) -> [UInt8] {
        let count = width * height
        guard let skin = medianColor(
            colors: colors,
            person: person,
            width: width,
            height: height,
            rect: region.skinSample
        ), let hair = medianColor(
            colors: colors,
            person: person,
            width: width,
            height: height,
            rect: region.crown
        ), distance(skin, hair) >= minimumSeparation else {
            return [UInt8](repeating: 0, count: count)
        }

        let clothes = medianColor(
            colors: colors,
            person: person,
            width: width,
            height: height,
            rect: region.clothesSample
        )
        let clothesAreDistinct = clothes.map { distance($0, hair) >= minimumSeparation } ?? false

        func matches(_ pixel: HairRGB) -> Bool {
            let fromHair = distance(pixel, hair)
            let fromSkin = distance(pixel, skin)
            guard fromHair + hairMargin < fromSkin, fromHair <= maxHairDistance else { return false }
            if clothesAreDistinct, let clothes, distance(pixel, clothes) + hairMargin <= fromHair {
                return false
            }
            return true
        }

        var dyed = [Bool](repeating: false, count: count)
        var queue = [Int]()
        queue.reserveCapacity(count / 8)
        var head = 0

        func consider(index: Int, x: Int, y: Int) -> Bool {
            if dyed[index] || person[index] < personMinimum { return false }
            let point = CGPoint(x: normX(x, width: width), y: normY(y, height: height))
            if region.protected.contains(point) || !region.search.contains(point) { return false }
            return matches(colors[index])
        }

        for y in 0..<height {
            for x in 0..<width {
                let index = (y * width) + x
                let point = CGPoint(x: normX(x, width: width), y: normY(y, height: height))
                guard region.crown.contains(point), consider(index: index, x: x, y: y) else { continue }
                dyed[index] = true
                queue.append(index)
            }
        }

        while head < queue.count {
            let index = queue[head]
            head += 1
            let x = index % width
            let y = index / width
            for dy in -1...1 {
                for dx in -1...1 where dx != 0 || dy != 0 {
                    let nx = x + dx
                    let ny = y + dy
                    guard nx >= 0, ny >= 0, nx < width, ny < height else { continue }
                    let neighbor = (ny * width) + nx
                    guard consider(index: neighbor, x: nx, y: ny) else { continue }
                    dyed[neighbor] = true
                    queue.append(neighbor)
                }
            }
        }

        var output = [UInt8](repeating: 0, count: count)
        for index in output.indices where dyed[index] {
            output[index] = person[index]
        }
        return output
    }

    private static func medianColor(
        colors: [HairRGB],
        person: [UInt8],
        width: Int,
        height: Int,
        rect: CGRect
    ) -> HairRGB? {
        var red = [Float]()
        var green = [Float]()
        var blue = [Float]()
        for y in 0..<height {
            for x in 0..<width {
                let index = (y * width) + x
                guard person[index] >= personMinimum else { continue }
                let point = CGPoint(x: normX(x, width: width), y: normY(y, height: height))
                guard rect.contains(point) else { continue }
                red.append(colors[index].r)
                green.append(colors[index].g)
                blue.append(colors[index].b)
            }
        }
        guard red.count >= minimumSampleCount,
              let r = median(red),
              let g = median(green),
              let b = median(blue) else {
            return nil
        }
        return HairRGB(r: r, g: g, b: b)
    }

    private static func median(_ values: [Float]) -> Float? {
        guard !values.isEmpty else { return nil }
        let sorted = values.sorted()
        let middle = sorted.count / 2
        if sorted.count.isMultiple(of: 2) {
            return (sorted[middle - 1] + sorted[middle]) / 2
        }
        return sorted[middle]
    }

    private static func distance(_ lhs: HairRGB, _ rhs: HairRGB) -> Float {
        let dr = lhs.r - rhs.r
        let dg = lhs.g - rhs.g
        let db = lhs.b - rhs.b
        return ((dr * dr) + (dg * dg) + (db * db)).squareRoot()
    }

    private static func normX(_ x: Int, width: Int) -> CGFloat {
        (CGFloat(x) + 0.5) / CGFloat(width)
    }

    private static func normY(_ y: Int, height: Int) -> CGFloat {
        1 - ((CGFloat(y) + 0.5) / CGFloat(height))
    }
}

/// Reads an upright camera image into rows whose first row is the top.
enum HairImageSampler {
    private static let context = CIContext(options: [
        .workingColorSpace: CGColorSpaceCreateDeviceRGB(),
        .outputColorSpace: CGColorSpaceCreateDeviceRGB(),
    ])

    /// `CIContext.render` does not document whether row 0 is the top. Measure it once.
    private static let bitmapRowZeroIsTop: Bool = {
        let width = 1
        let height = 2
        guard let context = CGContext(
            data: nil,
            width: width,
            height: height,
            bitsPerComponent: 8,
            bytesPerRow: 0,
            space: CGColorSpaceCreateDeviceRGB(),
            bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue
        ) else {
            return true
        }
        context.setFillColor(CGColor(srgbRed: 0, green: 0, blue: 1, alpha: 1))
        context.fill(CGRect(x: 0, y: 0, width: 1, height: 2))
        context.setFillColor(CGColor(srgbRed: 1, green: 0, blue: 0, alpha: 1))
        context.fill(CGRect(x: 0, y: 1, width: 1, height: 1))
        guard let rendered = context.makeImage() else { return true }
        var bytes = [UInt8](repeating: 0, count: 8)
        let wrote = bytes.withUnsafeMutableBytes { raw -> Bool in
            guard let base = raw.baseAddress else { return false }
            Self.context.render(
                CIImage(cgImage: rendered),
                toBitmap: base,
                rowBytes: 4,
                bounds: CGRect(x: 0, y: 0, width: 1, height: 2),
                format: .RGBA8,
                colorSpace: CGColorSpaceCreateDeviceRGB()
            )
            return true
        }
        guard wrote else { return true }
        return bytes[0] > 200 && bytes[2] < 80
    }()

    static func colors(from image: CIImage, width: Int, height: Int) -> [HairRGB]? {
        guard width > 0, height > 0 else { return nil }
        let extent = image.extent
        guard extent.width > 1, extent.height > 1, extent.width.isFinite, extent.height.isFinite else {
            return nil
        }
        let bounds = CGRect(x: 0, y: 0, width: CGFloat(width), height: CGFloat(height))
        let scaled = image
            .transformed(by: CGAffineTransform(translationX: -extent.origin.x, y: -extent.origin.y))
            .transformed(by: CGAffineTransform(
                scaleX: CGFloat(width) / extent.width,
                y: CGFloat(height) / extent.height
            ))
            .cropped(to: bounds)
        var bytes = [UInt8](repeating: 0, count: width * height * 4)
        let wrote = bytes.withUnsafeMutableBytes { raw -> Bool in
            guard let base = raw.baseAddress else { return false }
            context.render(
                scaled,
                toBitmap: base,
                rowBytes: width * 4,
                bounds: bounds,
                format: .RGBA8,
                colorSpace: CGColorSpaceCreateDeviceRGB()
            )
            return true
        }
        guard wrote else { return nil }

        var colors = [HairRGB]()
        colors.reserveCapacity(width * height)
        for row in 0..<height {
            let sourceRow = bitmapRowZeroIsTop ? row : (height - 1 - row)
            for column in 0..<width {
                let offset = ((sourceRow * width) + column) * 4
                colors.append(HairRGB(
                    r: Float(bytes[offset]) / 255,
                    g: Float(bytes[offset + 1]) / 255,
                    b: Float(bytes[offset + 2]) / 255
                ))
            }
        }
        return colors
    }
}

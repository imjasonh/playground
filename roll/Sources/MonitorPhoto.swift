import Foundation

/// An 8-bit RGBA bitmap stored row by row from the top-left corner.
///
/// The filter ignores alpha on input and writes opaque pixels.
struct RGBAImage: Equatable, Sendable {
    let width: Int
    let height: Int
    var pixels: [UInt8]

    init(width: Int, height: Int, pixels: [UInt8]) {
        precondition(width > 0 && height > 0, "image must not be empty")
        precondition(pixels.count == width * height * 4, "pixels must be RGBA")
        self.width = width
        self.height = height
        self.pixels = pixels
    }
}

/// A small seedable generator so that a style and its sensor noise repeat
/// exactly for a given seed.
struct SplitMix64: RandomNumberGenerator, Sendable {
    private var state: UInt64

    init(seed: UInt64) {
        state = seed
    }

    mutating func next() -> UInt64 {
        state &+= 0x9E37_79B9_7F4A_7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58_4761_CE4E_5B9D
        z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
        return z ^ (z >> 31)
    }
}

/// How a phone photo of a monitor differs from a clean screenshot.
///
/// Positions and radii use normalized coordinates: x runs from -1 at the
/// left edge to 1 at the right edge, and y uses the same scale, so it runs
/// from -height/width at the top to height/width at the bottom.
struct MonitorPhotoStyle: Equatable, Sendable {
    /// Camera roll. Positive values turn the screen counterclockwise.
    var rotationDegrees: Float
    /// How far the camera crops into the screen. 1 shows the whole screen.
    var zoom: Float
    /// Perspective from holding the phone off-axis. Positive x makes the
    /// right side of the screen look farther away.
    var keystoneX: Float
    var keystoneY: Float
    /// Where the photo is centered on the screen.
    var offsetX: Float
    var offsetY: Float
    /// Phone lens barrel distortion.
    var barrel: Float
    /// Mix toward the defocused copy at the center and, added on top, at
    /// the corners.
    var focusBlur: Float
    var edgeBlur: Float
    /// Red and blue fringing at the corners, in pixels of a 1500-pixel-wide
    /// image.
    var chromaticAberration: Float
    /// Amplitude of the moiré that the screen's subpixel grid makes against
    /// the camera sensor.
    var moireStrength: Float
    /// How far the subpixel grid's pitch is from the sensor's in each
    /// direction. Smaller magnitudes make wider stripes.
    var moireDetuneX: Float
    var moireDetuneY: Float
    /// Phase of the slow variation in moiré strength across the frame.
    var moirePatchPhase: Float
    /// A room light reflected in the glass.
    var glareX: Float
    var glareY: Float
    var glareRadius: Float
    var glareStrength: Float
    var glareColor: SIMD3<Float>
    /// Flat haze from light the glass scatters.
    var veil: Float
    /// What black pixels photograph as: a backlit LCD never reaches black.
    var blackLevel: SIMD3<Float>
    /// The camera's white balance applied to the screen's color. No channel
    /// should exceed 1, so white text doesn't clip.
    var whiteBalance: SIMD3<Float>
    /// Where the phone puts the screen's white, below clipping.
    var exposure: Float
    var saturation: Float
    /// Above 1 darkens midtones the way a phone exposes for bright text.
    var gamma: Float
    var vignette: Float
    /// Brightness loss toward one side, from the panel's viewing angle.
    var falloff: Float
    var falloffAngle: Float
    /// Glow around bright areas.
    var bloom: Float
    /// Standard deviation of sensor noise in dark areas.
    var noise: Float
    var noiseSeed: UInt64

    /// A plausible photo: each call with a different seed holds the phone a
    /// little differently, under a different light.
    static func random(seed: UInt64) -> MonitorPhotoStyle {
        var rng = SplitMix64(seed: seed)
        func uniform(_ range: ClosedRange<Float>) -> Float {
            Float.random(in: range, using: &rng)
        }
        func signed(_ range: ClosedRange<Float>) -> Float {
            Bool.random(using: &rng) ? uniform(range) : -uniform(range)
        }

        let warmLight = uniform(0...1) < 0.65
        let glareColor: SIMD3<Float> = warmLight ? [1.0, 0.78, 0.52] : [0.86, 0.93, 1.0]
        let whiteBalance: SIMD3<Float>
        switch uniform(0...1) {
        case ..<0.45:
            whiteBalance = [0.89, 0.94, 1.0]
        case ..<0.8:
            whiteBalance = [1.0, 0.95, 0.86]
        default:
            whiteBalance = [0.94, 1.0, 0.94]
        }
        let black = uniform(0.05...0.085)
        let blackTint: SIMD3<Float> = warmLight ? [1.12, 1.0, 0.88] : [0.92, 1.0, 1.12]

        return MonitorPhotoStyle(
            rotationDegrees: signed(0.6...2.0),
            zoom: uniform(1.05...1.11),
            keystoneX: signed(0.02...0.06),
            keystoneY: signed(0.01...0.04),
            offsetX: uniform(-0.03...0.03),
            offsetY: uniform(-0.03...0.03),
            barrel: uniform(0.02...0.05),
            focusBlur: uniform(0.4...0.65),
            edgeBlur: uniform(0.2...0.45),
            chromaticAberration: uniform(0.6...1.3),
            moireStrength: uniform(0.13...0.2),
            moireDetuneX: signed(0.06...0.13),
            moireDetuneY: signed(0.07...0.15),
            moirePatchPhase: uniform(0...(2 * .pi)),
            glareX: uniform(-0.7...0.7),
            glareY: uniform(-0.45...0.15),
            glareRadius: uniform(0.25...0.45),
            glareStrength: uniform(0.1...0.24),
            glareColor: glareColor,
            veil: uniform(0.015...0.04),
            blackLevel: blackTint * black,
            whiteBalance: whiteBalance,
            exposure: uniform(0.86...0.94),
            saturation: uniform(0.82...0.94),
            gamma: uniform(1.05...1.18),
            vignette: uniform(0.2...0.38),
            falloff: uniform(0.08...0.2),
            falloffAngle: uniform(0...(2 * .pi)),
            bloom: uniform(0.18...0.35),
            noise: uniform(0.016...0.03),
            noiseSeed: rng.next()
        )
    }
}

/// Makes a screenshot look like a phone photo of the monitor showing it.
enum MonitorPhotoFilter {
    static func apply(_ image: RGBAImage, style: MonitorPhotoStyle) -> RGBAImage {
        let width = image.width
        let height = image.height
        let count = width * height

        var sharp = [[Float]](repeating: [Float](repeating: 0, count: count), count: 3)
        image.pixels.withUnsafeBufferPointer { src in
            for index in 0..<count {
                for channel in 0..<3 {
                    sharp[channel][index] = Float(src[index * 4 + channel]) / 255
                }
            }
        }

        let softRadius = max(1, Int((Float(width) / 700).rounded()))
        let soft = sharp.map { plane in
            boxBlur(boxBlur(plane, width: width, height: height, radius: softRadius),
                    width: width, height: height, radius: softRadius)
        }
        let glow = Glow(sharp: sharp, width: width, height: height)

        var output = [UInt8](repeating: 255, count: count * 4)
        let geometry = Geometry(style: style, width: width, height: height)
        let rows = height
        let bands = min(rows, max(1, ProcessInfo.processInfo.activeProcessorCount * 4))

        output.withUnsafeMutableBufferPointer { out in
            let out = out
            DispatchQueue.concurrentPerform(iterations: bands) { band in
                let start = band * rows / bands
                let end = (band + 1) * rows / bands
                for y in start..<end {
                    renderRow(
                        y,
                        into: out,
                        sharp: sharp,
                        soft: soft,
                        glow: glow,
                        geometry: geometry,
                        style: style
                    )
                }
            }
        }
        return RGBAImage(width: width, height: height, pixels: output)
    }

    private struct Geometry {
        let width: Int
        let height: Int
        let aspect: Float
        let cosine: Float
        let sine: Float
        let zoom: Float
        let fringe: Float
        let pitchX: Float
        let pitchY: Float

        init(style: MonitorPhotoStyle, width: Int, height: Int) {
            self.width = width
            self.height = height
            aspect = Float(height) / Float(width)
            let radians = style.rotationDegrees * .pi / 180
            cosine = cos(radians)
            sine = sin(radians)
            zoom = style.zoom
            fringe = style.chromaticAberration / 750
            // The sensor samples once per output pixel. A subpixel grid whose
            // pitch is near that rate aliases to stripes a few pixels wide;
            // tying the pitch to the output size keeps the stripes the same
            // whatever resolution the screenshot was taken at.
            pitchX = style.zoom * (1 + style.moireDetuneX)
            pitchY = style.zoom * (1 + style.moireDetuneY)
        }

        /// Maps a normalized point in the photo to a pixel on the screen.
        func screenPoint(nx: Float, ny: Float, style: MonitorPhotoStyle) -> (u: Float, v: Float) {
            let distortion = 1 + style.barrel * (nx * nx + ny * ny)
            let px = nx * distortion
            let py = ny * distortion
            let qx = (cosine * px + sine * py) / zoom
            let qy = (-sine * px + cosine * py) / zoom
            let depth = 1 - style.keystoneX * qx - style.keystoneY * qy
            let sx = qx / depth + style.offsetX
            let sy = qy / depth + style.offsetY
            let u = (sx + 1) * 0.5 * Float(width) - 0.5
            let v = (sy / aspect + 1) * 0.5 * Float(height) - 0.5
            return (u, v)
        }
    }

    /// A blurred, downsampled copy of the screenshot's highlights.
    private struct Glow {
        let scale: Int
        let width: Int
        let height: Int
        let planes: [[Float]]

        init(sharp: [[Float]], width sourceWidth: Int, height sourceHeight: Int) {
            scale = max(4, sourceWidth / 240)
            width = max(1, sourceWidth / scale)
            height = max(1, sourceHeight / scale)
            var planes = [[Float]](repeating: [Float](repeating: 0, count: width * height), count: 3)
            let area = Float(scale * scale)
            for y in 0..<height {
                for x in 0..<width {
                    var sum = SIMD3<Float>(repeating: 0)
                    for dy in 0..<scale {
                        let row = min(sourceHeight - 1, y * scale + dy) * sourceWidth
                        for dx in 0..<scale {
                            let index = row + min(sourceWidth - 1, x * scale + dx)
                            let color = SIMD3(sharp[0][index], sharp[1][index], sharp[2][index])
                            let luma = luminance(color)
                            let excess = max(0, luma - 0.55) / 0.45
                            sum += color * excess
                        }
                    }
                    for channel in 0..<3 {
                        planes[channel][y * width + x] = sum[channel] / area
                    }
                }
            }
            let (glowWidth, glowHeight) = (width, height)
            self.planes = planes.map { plane in
                var blurred = plane
                for _ in 0..<3 {
                    blurred = MonitorPhotoFilter.boxBlur(blurred, width: glowWidth, height: glowHeight, radius: 2)
                }
                return blurred
            }
        }

        func sample(u: Float, v: Float) -> SIMD3<Float> {
            let gu = (u + 0.5) / Float(scale) - 0.5
            let gv = (v + 0.5) / Float(scale) - 0.5
            return SIMD3(
                bilinear(planes[0], width: width, height: height, u: gu, v: gv),
                bilinear(planes[1], width: width, height: height, u: gu, v: gv),
                bilinear(planes[2], width: width, height: height, u: gu, v: gv)
            )
        }
    }

    private static let bezel: SIMD3<Float> = [0.025, 0.025, 0.03]

    private static func renderRow(
        _ y: Int,
        into out: UnsafeMutableBufferPointer<UInt8>,
        sharp: [[Float]],
        soft: [[Float]],
        glow: Glow,
        geometry: Geometry,
        style: MonitorPhotoStyle
    ) {
        let width = geometry.width
        let height = geometry.height
        let aspect = geometry.aspect
        var rng = SplitMix64(seed: style.noiseSeed ^ (UInt64(y) &* 0xD134_2543_DE82_EF95))
        let ny = ((Float(y) + 0.5) / Float(height) * 2 - 1) * aspect
        let falloffX = cos(style.falloffAngle)
        let falloffY = sin(style.falloffAngle)
        let centerU = Float(width) * 0.5 - 0.5
        let centerV = Float(height) * 0.5 - 0.5
        let twoPi = 2 * Float.pi
        let one = SIMD3<Float>(repeating: 1)

        for x in 0..<width {
            let nx = (Float(x) + 0.5) / Float(width) * 2 - 1
            let radius2 = nx * nx + ny * ny
            let (u, v) = geometry.screenPoint(nx: nx, ny: ny, style: style)

            let defocus = min(1, style.focusBlur + style.edgeBlur * radius2)
            let fringe = geometry.fringe * radius2
            let redU = centerU + (u - centerU) * (1 + fringe)
            let redV = centerV + (v - centerV) * (1 + fringe)
            let blueU = centerU + (u - centerU) * (1 - fringe)
            let blueV = centerV + (v - centerV) * (1 - fringe)
            func lens(_ channel: Int, _ su: Float, _ sv: Float) -> Float {
                let crisp = bilinear(sharp[channel], width: width, height: height, u: su, v: sv)
                let blurry = bilinear(soft[channel], width: width, height: height, u: su, v: sv)
                return crisp + (blurry - crisp) * defocus
            }
            var color = SIMD3(lens(0, redU, redV), lens(1, u, v), lens(2, blueU, blueV))

            let edge = min(u + 0.5, Float(width) - 0.5 - u, v + 0.5, Float(height) - 0.5 - v)
            let coverage = min(1, max(0, edge + 0.5))

            // Point-sampling the subpixel grid at each pixel is what aliases
            // it: the red, green, and blue stripes sit a third of a pixel
            // apart, so their beats land a third of a period apart and the
            // stripes come out in color.
            let gridU = u * geometry.pitchX
            let gridV = v * geometry.pitchY
            let rowMask = cos(twoPi * gridV)
            let patch = 0.55 + 0.45 * sin(nx * 2.7 + style.moirePatchPhase) * sin(ny * 3.4 - style.moirePatchPhase)
            let luma = luminance(color)
            let amount = style.moireStrength * patch * (0.2 + 0.8 * luma) * coverage
            for channel in 0..<3 {
                let stripe = cos(twoPi * (gridU - Float(channel) / 3))
                color[channel] *= 1 + amount * (0.75 * stripe + 0.35 * rowMask)
            }

            color = color * coverage + bezel * (1 - coverage)

            let gray = luminance(color)
            color = SIMD3(repeating: gray) + (color - SIMD3(repeating: gray)) * style.saturation
            let bloomAmount = style.bloom * coverage
            let halo = glow.sample(u: u, v: v) * bloomAmount
            color = one - (one - color) * (one - halo)
            color = SIMD3(
                pow(max(0, color.x), style.gamma),
                pow(max(0, color.y), style.gamma),
                pow(max(0, color.z), style.gamma)
            )
            color = style.blackLevel + color * (one - style.blackLevel)
            color *= style.whiteBalance * style.exposure

            let dx = nx - style.glareX
            let dy = ny - style.glareY
            let distance2 = dx * dx + dy * dy
            let sigma2 = style.glareRadius * style.glareRadius
            let glare = style.glareStrength * (exp(-distance2 / (2 * sigma2)) + 0.3 * exp(-distance2 / (12 * sigma2)))
            let light = style.glareColor * glare + SIMD3(repeating: style.veil)
            color = one - (one - color) * (one - light)

            let side = (nx * falloffX + ny * falloffY + 1) * 0.5
            color *= (1 - style.vignette * radius2 * radius2 * 0.6 - style.vignette * radius2 * 0.4)
                * (1 - style.falloff * side)

            let brightness = luminance(color)
            let sigma = style.noise * (0.45 + (1 - min(1, brightness)))
            let grain = gaussian(&rng) * sigma
            let chroma = SIMD3(gaussian(&rng), gaussian(&rng), gaussian(&rng)) * (sigma * 0.35)
            color += SIMD3(repeating: grain) + chroma

            let base = (y * width + x) * 4
            out[base] = byte(color.x)
            out[base + 1] = byte(color.y)
            out[base + 2] = byte(color.z)
            out[base + 3] = 255
        }
    }

    private static func luminance(_ color: SIMD3<Float>) -> Float {
        0.2126 * color.x + 0.7152 * color.y + 0.0722 * color.z
    }

    private static func byte(_ value: Float) -> UInt8 {
        UInt8(max(0, min(255, (value * 255).rounded())))
    }

    /// An approximately normal sample: the Irwin–Hall sum of four uniforms.
    private static func gaussian(_ rng: inout SplitMix64) -> Float {
        var sum: Float = 0
        for _ in 0..<4 {
            sum += Float(rng.next() >> 40) / Float(1 << 24)
        }
        return (sum - 2) * 1.732_05
    }

    private static func bilinear(_ plane: [Float], width: Int, height: Int, u: Float, v: Float) -> Float {
        let cu = min(Float(width - 1), max(0, u))
        let cv = min(Float(height - 1), max(0, v))
        let x0 = Int(cu)
        let y0 = Int(cv)
        let x1 = min(width - 1, x0 + 1)
        let y1 = min(height - 1, y0 + 1)
        let fx = cu - Float(x0)
        let fy = cv - Float(y0)
        let top = plane[y0 * width + x0] + (plane[y0 * width + x1] - plane[y0 * width + x0]) * fx
        let bottom = plane[y1 * width + x0] + (plane[y1 * width + x1] - plane[y1 * width + x0]) * fx
        return top + (bottom - top) * fy
    }

    static func boxBlur(_ plane: [Float], width: Int, height: Int, radius: Int) -> [Float] {
        guard radius > 0 else {
            return plane
        }
        let horizontal = blurPass(plane, count: height, length: width, stride: 1, lineStride: width, radius: radius)
        return blurPass(horizontal, count: width, length: height, stride: width, lineStride: 1, radius: radius)
    }

    /// One running-sum box blur along every line, clamping at the edges.
    private static func blurPass(
        _ input: [Float],
        count: Int,
        length: Int,
        stride: Int,
        lineStride: Int,
        radius: Int
    ) -> [Float] {
        var output = [Float](repeating: 0, count: input.count)
        let scale = 1 / Float(2 * radius + 1)
        input.withUnsafeBufferPointer { src in
            output.withUnsafeMutableBufferPointer { dst in
                for line in 0..<count {
                    let origin = line * lineStride
                    func at(_ i: Int) -> Float {
                        src[origin + min(length - 1, max(0, i)) * stride]
                    }
                    var sum: Float = 0
                    for i in -radius...radius {
                        sum += at(i)
                    }
                    for i in 0..<length {
                        dst[origin + i * stride] = sum * scale
                        sum += at(i + radius + 1) - at(i - radius)
                    }
                }
            }
        }
        return output
    }
}

import UIKit

/// Square episode art drawn on device from the topic.
///
/// Headless Image Playground generation does not run on iOS 27, so each
/// episode gets a cover composed here and stored next to its audio.
enum BlatherArtwork {
    static let fileName = "cover.jpg"
    /// Stable art for the show header.
    static let showImage: UIImage = render(topic: "Blather", pixels: 512)

    private static var files: [String: UIImage] = [:]

    static func render(topic: String, pixels: Int) -> UIImage {
        let side = max(64, pixels)
        let format = UIGraphicsImageRendererFormat()
        format.scale = 1
        format.opaque = true
        let renderer = UIGraphicsImageRenderer(size: CGSize(width: side, height: side), format: format)
        return renderer.image { context in
            draw(topic: topic, in: context.cgContext, side: CGFloat(side))
        }
    }

    static func jpeg(topic: String, pixels: Int = 768) -> Data {
        render(topic: topic, pixels: pixels).jpegData(compressionQuality: 0.86) ?? Data()
    }

    /// Loads a saved cover, or draws one when the file is not there yet.
    static func image(at url: URL, topic: String) -> UIImage {
        if let cached = files[url.path] {
            return cached
        }
        let image = UIImage(contentsOfFile: url.path) ?? render(topic: topic, pixels: 768)
        files[url.path] = image
        return image
    }

    private static func draw(topic: String, in ctx: CGContext, side: CGFloat) {
        var rng = BlatherArtworkRNG(topic: topic)
        let palette = palettes[rng.int(palettes.count)]
        ctx.setFillColor(palette.background.cgColor)
        ctx.fill(CGRect(x: 0, y: 0, width: side, height: side))

        for index in 0..<3 {
            let color = palette.shapes[index % palette.shapes.count]
            ctx.setFillColor(color.withAlphaComponent(0.92).cgColor)
            let radius = side * (0.26 + 0.24 * rng.unit())
            let center = CGPoint(
                x: side * rng.unit(),
                y: side * (0.08 + 0.5 * rng.unit())
            )
            ctx.fillEllipse(in: CGRect(
                x: center.x - radius,
                y: center.y - radius,
                width: radius * 2,
                height: radius * 2
            ))
        }

        if let gradient = CGGradient(
            colorsSpace: CGColorSpaceCreateDeviceRGB(),
            colors: [
                palette.background.withAlphaComponent(0).cgColor,
                palette.background.cgColor,
            ] as CFArray,
            locations: [0, 1]
        ) {
            ctx.drawLinearGradient(
                gradient,
                start: CGPoint(x: 0, y: side * 0.38),
                end: CGPoint(x: 0, y: side * 0.72),
                options: []
            )
        }
        ctx.setFillColor(palette.background.cgColor)
        ctx.fill(CGRect(x: 0, y: side * 0.72, width: side, height: side * 0.28))

        let pad = side * 0.07
        drawWordmark(palette: palette, pad: pad, side: side, in: ctx)
        drawTitle(displayTitle(topic), pad: pad, side: side)
    }

    private static func drawWordmark(palette: Palette, pad: CGFloat, side: CGFloat, in ctx: CGContext) {
        let font = UIFont.systemFont(ofSize: side * 0.034, weight: .heavy)
        let attributes: [NSAttributedString.Key: Any] = [
            .font: font,
            .foregroundColor: UIColor.white,
            .kern: side * 0.004,
        ]
        let text = "BLATHER" as NSString
        let textSize = text.size(withAttributes: attributes)
        let pill = CGRect(
            x: pad,
            y: pad,
            width: textSize.width + pad * 0.85,
            height: textSize.height + pad * 0.42
        )
        ctx.setFillColor(palette.background.withAlphaComponent(0.9).cgColor)
        ctx.addPath(UIBezierPath(roundedRect: pill, cornerRadius: pill.height / 2).cgPath)
        ctx.fillPath()
        text.draw(
            at: CGPoint(
                x: pill.midX - textSize.width / 2,
                y: pill.midY - textSize.height / 2
            ),
            withAttributes: attributes
        )
    }

    private static func drawTitle(_ title: String, pad: CGFloat, side: CGFloat) {
        let width = side - pad * 2
        let maxHeight = side * 0.28
        var fontSize = side * 0.092
        let minimum = side * 0.05
        var fitted = NSAttributedString(string: title)
        var fittedHeight = maxHeight
        while fontSize >= minimum {
            let style = NSMutableParagraphStyle()
            style.lineBreakMode = .byWordWrapping
            style.alignment = .left
            let text = NSAttributedString(
                string: title,
                attributes: [
                    .font: UIFont.systemFont(ofSize: fontSize, weight: .bold),
                    .foregroundColor: UIColor.white,
                    .paragraphStyle: style,
                ]
            )
            let bounds = text.boundingRect(
                with: CGSize(width: width, height: .greatestFiniteMagnitude),
                options: [.usesLineFragmentOrigin, .usesFontLeading],
                context: nil
            )
            fitted = text
            fittedHeight = min(maxHeight, ceil(bounds.height))
            if bounds.height <= maxHeight {
                break
            }
            fontSize -= 1
        }
        let rect = CGRect(x: pad, y: side - pad - fittedHeight, width: width, height: fittedHeight)
        fitted.draw(with: rect, options: [.usesLineFragmentOrigin], context: nil)
    }

    /// Keeps the cover to a short title. The player still shows the full topic.
    private static func displayTitle(_ topic: String) -> String {
        let trimmed = topic.trimmingCharacters(in: .whitespacesAndNewlines)
        guard trimmed.count > 64 else { return trimmed.isEmpty ? "Blather" : trimmed }
        let end = trimmed.index(trimmed.startIndex, offsetBy: 64)
        let prefix = trimmed[..<end]
        if let space = prefix.lastIndex(of: " "), space > trimmed.startIndex {
            return String(prefix[..<space])
        }
        return String(prefix)
    }

    private struct Palette {
        var background: UIColor
        var shapes: [UIColor]
    }

    private static let palettes: [Palette] = [
        Palette(background: rgb(0.07, 0.08, 0.11), shapes: [rgb(1.00, 0.42, 0.29), rgb(0.95, 0.82, 0.64)]),
        Palette(background: rgb(0.06, 0.14, 0.11), shapes: [rgb(0.78, 0.95, 0.35), rgb(0.84, 0.89, 0.83)]),
        Palette(background: rgb(0.05, 0.10, 0.20), shapes: [rgb(0.94, 0.76, 0.29), rgb(0.56, 0.79, 0.90)]),
        Palette(background: rgb(0.16, 0.06, 0.12), shapes: [rgb(1.00, 0.56, 0.67), rgb(1.00, 0.90, 0.82)]),
        Palette(background: rgb(0.11, 0.07, 0.19), shapes: [rgb(0.72, 0.63, 1.00), rgb(1.00, 0.69, 0.52)]),
        Palette(background: rgb(0.10, 0.12, 0.14), shapes: [rgb(0.18, 0.77, 0.71), rgb(0.91, 0.95, 0.94)]),
        Palette(background: rgb(0.14, 0.09, 0.06), shapes: [rgb(1.00, 0.72, 0.01), rgb(0.98, 0.52, 0.00)]),
        Palette(background: rgb(0.04, 0.06, 0.13), shapes: [rgb(0.48, 0.64, 1.00), rgb(0.84, 0.89, 1.00)]),
    ]

    private static func rgb(_ red: CGFloat, _ green: CGFloat, _ blue: CGFloat) -> UIColor {
        UIColor(red: red, green: green, blue: blue, alpha: 1)
    }
}

/// Deterministic mixer so a topic always paints the same cover.
private struct BlatherArtworkRNG {
    private var state: UInt64

    init(topic: String) {
        var hash: UInt64 = 14_695_981_039_346_656_037
        for byte in topic.utf8 {
            hash ^= UInt64(byte)
            hash &*= 1_099_511_628_211
        }
        state = hash == 0 ? 0xA5A5_A5A5_A5A5_A5A5 : hash
    }

    mutating func next() -> UInt64 {
        state &+= 0x9E37_79B9_7F4A_7C15
        var mixed = state
        mixed = (mixed ^ (mixed >> 30)) &* 0xBF58_476D_1CE4_E5B9
        mixed = (mixed ^ (mixed >> 27)) &* 0x94D0_49BB_1331_11EB
        return mixed ^ (mixed >> 31)
    }

    mutating func unit() -> CGFloat {
        CGFloat(next() % 10_000) / 10_000
    }

    mutating func int(_ upper: Int) -> Int {
        guard upper > 0 else { return 0 }
        return Int(next() % UInt64(upper))
    }
}

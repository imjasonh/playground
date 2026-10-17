import CoreGraphics
import CoreText
import Foundation
import Metal

struct VRMenuContent: Equatable {
    var hovered: VRMenuItem?
    var passthroughOn: Bool
    var passthroughAvailable: Bool
    var statsOn: Bool
    var scene: VRSceneKind
}

struct VRCalibrationRow: Equatable {
    var parameter: VRCalibrationParameter
    var value: String
}

struct VRCalibrationContent: Equatable {
    var rows: [VRCalibrationRow]
    var selected: VRCalibrationParameter
    var hovered: VRGazeTarget?
}

struct VRSceneSignContent: Equatable {
    var current: VRSceneKind
    var hovered: VRSceneKind?
}

/// What a panel shows. Equal content reuses the painted texture.
enum VRPanelContent: Equatable {
    case menu(VRMenuContent)
    case sceneSign(VRSceneSignContent)
    case calibration(VRCalibrationContent)
    case stats([String])
    case countdown(seconds: Int, subtitle: String)
    case message(String)
}

/// Paints panel contents with Core Graphics and Core Text on a background
/// queue and hands back Metal textures. The render thread asks for a slot's
/// texture every frame; when the content changed it gets the previous
/// texture until the repaint lands, so it never waits on drawing.
final class VRPanelPainter: @unchecked Sendable {
    enum Slot: Hashable {
        case menu
        case sceneSign
        case calibration
        case stats
        case countdown
        case message
    }

    private struct State {
        var requested: [Slot: VRPanelContent] = [:]
        var painted: [Slot: (content: VRPanelContent, texture: MTLTexture)] = [:]
        var painting: Set<Slot> = []
    }

    /// Texture pixels per meter of panel.
    static let pixelsPerMeter: Float = 1600

    private let device: MTLDevice
    private let uploadQueue: MTLCommandQueue?
    private let queue = DispatchQueue(label: "PhoneVR.panels", qos: .userInitiated)
    private let state = VRLocked(State())

    init(device: MTLDevice) {
        self.device = device
        uploadQueue = device.makeCommandQueue()
        uploadQueue?.label = "PhoneVR panels"
    }

    static func size(of slot: Slot) -> SIMD2<Float> {
        switch slot {
        case .menu: return VRPanelLayouts.menuSize
        case .sceneSign: return VRPanelLayouts.sceneSignSize
        case .calibration: return VRPanelLayouts.calibrationSize
        case .stats: return VRPanelLayouts.statsSize
        case .countdown: return VRPanelLayouts.countdownSize
        case .message: return VRPanelLayouts.messageSize
        }
    }

    /// The newest texture painted for `slot`, scheduling a repaint when `content` differs.
    func texture(for slot: Slot, content: VRPanelContent) -> MTLTexture? {
        let (texture, schedule) = state.withLock { s -> (MTLTexture?, Bool) in
            if let painted = s.painted[slot], painted.content == content { return (painted.texture, false) }
            s.requested[slot] = content
            guard !s.painting.contains(slot) else { return (s.painted[slot]?.texture, false) }
            s.painting.insert(slot)
            return (s.painted[slot]?.texture, true)
        }
        if schedule {
            queue.async { [weak self] in self?.paintLoop(slot) }
        }
        return texture
    }

    private func paintLoop(_ slot: Slot) {
        while true {
            guard let content = state.withLock({ $0.requested[slot] }) else {
                state.withLock { _ = $0.painting.remove(slot) }
                return
            }
            let texture = paint(content, size: Self.size(of: slot))
            let done = state.withLock { s -> Bool in
                if let texture { s.painted[slot] = (content, texture) }
                if s.requested[slot] == content {
                    s.painting.remove(slot)
                    return true
                }
                return false
            }
            if done { return }
        }
    }

    // MARK: - Painting

    private func paint(_ content: VRPanelContent, size: SIMD2<Float>) -> MTLTexture? {
        let width = Int(size.x * Self.pixelsPerMeter)
        let height = Int(size.y * Self.pixelsPerMeter)
        guard let space = CGColorSpace(name: CGColorSpace.sRGB),
              let context = CGContext(
                  data: nil, width: width, height: height, bitsPerComponent: 8, bytesPerRow: width * 4, space: space,
                  bitmapInfo: CGImageAlphaInfo.premultipliedFirst.rawValue | CGBitmapInfo.byteOrder32Little.rawValue
              )
        else { return nil }
        let canvas = Canvas(context: context, width: CGFloat(width), height: CGFloat(height))
        switch content {
        case .menu(let menu): drawMenu(menu, on: canvas)
        case .sceneSign(let sign): drawSceneSign(sign, on: canvas)
        case .calibration(let calibration): drawCalibration(calibration, on: canvas)
        case .stats(let lines): drawStats(lines, on: canvas)
        case .countdown(let seconds, let subtitle): drawCountdown(seconds, subtitle: subtitle, on: canvas)
        case .message(let text): drawMessage(text, on: canvas)
        }
        return upload(context: context, width: width, height: height)
    }

    private func upload(context: CGContext, width: Int, height: Int) -> MTLTexture? {
        guard let data = context.data else { return nil }
        let descriptor = MTLTextureDescriptor.texture2DDescriptor(pixelFormat: .bgra8Unorm_srgb, width: width, height: height, mipmapped: true)
        descriptor.usage = [.shaderRead, .renderTarget]
        descriptor.storageMode = .shared
        guard let texture = device.makeTexture(descriptor: descriptor) else { return nil }
        texture.replace(region: MTLRegionMake2D(0, 0, width, height), mipmapLevel: 0, withBytes: data, bytesPerRow: context.bytesPerRow)
        if let commandBuffer = uploadQueue?.makeCommandBuffer(), let blit = commandBuffer.makeBlitCommandEncoder() {
            blit.generateMipmaps(for: texture)
            blit.endEncoding()
            commandBuffer.commit()
            commandBuffer.waitUntilCompleted()
        }
        return texture
    }

    private enum Ink {
        static let background = CGColor(srgbRed: 0.067, green: 0.082, blue: 0.11, alpha: 0.9)
        static let button = CGColor(srgbRed: 0.15, green: 0.18, blue: 0.23, alpha: 1)
        static let buttonHover = CGColor(srgbRed: 0.18, green: 0.47, blue: 0.45, alpha: 1)
        static let buttonOn = CGColor(srgbRed: 0.2, green: 0.3, blue: 0.42, alpha: 1)
        static let accent = CGColor(srgbRed: 0.31, green: 0.82, blue: 0.77, alpha: 1)
        static let text = CGColor(srgbRed: 1, green: 1, blue: 1, alpha: 1)
        static let secondary = CGColor(srgbRed: 0.63, green: 0.68, blue: 0.75, alpha: 1)
        static let disabled = CGColor(srgbRed: 0.45, green: 0.48, blue: 0.53, alpha: 1)
        static let danger = CGColor(srgbRed: 0.96, green: 0.4, blue: 0.4, alpha: 1)
    }

    /// Draws in panel texture coordinates (origin top left, v down) on a
    /// bitmap whose first row is the top of the image.
    private struct Canvas {
        let context: CGContext
        let width: CGFloat
        let height: CGFloat

        func rect(_ r: VRRect) -> CGRect {
            CGRect(
                x: CGFloat(r.x) * width,
                y: (1 - CGFloat(r.y) - CGFloat(r.height)) * height,
                width: CGFloat(r.width) * width,
                height: CGFloat(r.height) * height
            )
        }

        func fill(_ r: CGRect, color: CGColor, radius: CGFloat) {
            context.addPath(CGPath(roundedRect: r, cornerWidth: radius, cornerHeight: radius, transform: nil))
            context.setFillColor(color)
            context.fillPath()
        }

        func stroke(_ r: CGRect, color: CGColor, radius: CGFloat, width lineWidth: CGFloat) {
            context.addPath(CGPath(roundedRect: r.insetBy(dx: lineWidth / 2, dy: lineWidth / 2), cornerWidth: radius, cornerHeight: radius, transform: nil))
            context.setStrokeColor(color)
            context.setLineWidth(lineWidth)
            context.strokePath()
        }

        enum Alignment {
            case leading
            case center
            case trailing
        }

        /// Draws one line of text, shrinking it to fit the width of `r`.
        func text(_ string: String, in r: CGRect, size: CGFloat, bold: Bool = false, color: CGColor, alignment: Alignment = .center) {
            func makeLine(_ size: CGFloat) -> CTLine {
                let font = CTFontCreateUIFontForLanguage(bold ? .emphasizedSystem : .system, size, nil)
                    ?? CTFontCreateWithName("Helvetica" as CFString, size, nil)
                let attributes: [NSAttributedString.Key: Any] = [
                    NSAttributedString.Key(kCTFontAttributeName as String): font,
                    NSAttributedString.Key(kCTForegroundColorAttributeName as String): color,
                ]
                return CTLineCreateWithAttributedString(NSAttributedString(string: string, attributes: attributes) as CFAttributedString)
            }
            var line = makeLine(size)
            let natural = CGFloat(CTLineGetTypographicBounds(line, nil, nil, nil))
            if natural > r.width, r.width > 0 {
                line = makeLine(size * r.width / natural)
            }
            var ascent: CGFloat = 0
            var descent: CGFloat = 0
            var leading: CGFloat = 0
            let textWidth = CGFloat(CTLineGetTypographicBounds(line, &ascent, &descent, &leading))
            let x: CGFloat
            switch alignment {
            case .leading: x = r.minX
            case .center: x = r.midX - textWidth / 2
            case .trailing: x = r.maxX - textWidth
            }
            context.textPosition = CGPoint(x: x, y: r.midY - (ascent - descent) / 2)
            CTLineDraw(line, context)
        }

        func background() {
            fill(CGRect(x: 0, y: 0, width: width, height: height), color: Ink.background, radius: height * 0.06)
        }
    }

    private func drawMenu(_ menu: VRMenuContent, on canvas: Canvas) {
        canvas.background()
        canvas.text("Phone VR", in: canvas.rect(VRPanelLayouts.menuTitle), size: canvas.height * 0.085, bold: true, color: Ink.text)
        for button in VRPanelLayouts.menuButtons {
            guard case .menu(let item) = button.target else { continue }
            let r = canvas.rect(button.frame)
            let hovered = menu.hovered == item
            let on: Bool
            let title: String
            var color = Ink.text
            switch item {
            case .recenter:
                title = "Recenter"
                on = false
            case .passthrough:
                title = menu.passthroughAvailable ? (menu.passthroughOn ? "Passthrough: On" : "Passthrough: Off") : "Passthrough: No camera"
                on = menu.passthroughOn
                if !menu.passthroughAvailable { color = Ink.disabled }
            case .stats:
                title = menu.statsOn ? "Stats: On" : "Stats: Off"
                on = menu.statsOn
            case .scene:
                title = menu.scene.next.menuTitle
                on = false
            case .close:
                title = "Close"
                on = false
            case .exit:
                title = "Exit VR"
                on = false
                color = Ink.danger
            }
            canvas.fill(r, color: hovered ? Ink.buttonHover : (on ? Ink.buttonOn : Ink.button), radius: r.height * 0.22)
            if hovered { canvas.stroke(r, color: Ink.accent, radius: r.height * 0.22, width: 4) }
            canvas.text(title, in: r, size: r.height * 0.3, bold: hovered, color: color)
        }
    }

    private func drawSceneSign(_ sign: VRSceneSignContent, on canvas: Canvas) {
        canvas.background()
        canvas.text("Scene", in: canvas.rect(VRPanelLayouts.sceneSignTitle), size: canvas.height * 0.08, bold: true, color: Ink.text)
        for button in VRPanelLayouts.sceneSignButtons {
            guard case .sceneSign(let scene) = button.target else { continue }
            let r = canvas.rect(button.frame)
            let hovered = sign.hovered == scene
            let on = sign.current == scene
            canvas.fill(r, color: hovered ? Ink.buttonHover : (on ? Ink.buttonOn : Ink.button), radius: r.height * 0.22)
            if hovered { canvas.stroke(r, color: Ink.accent, radius: r.height * 0.22, width: 4) }
            canvas.text(scene.title, in: r, size: r.height * 0.36, bold: hovered || on, color: Ink.text)
        }
    }

    private func drawCalibration(_ calibration: VRCalibrationContent, on canvas: Canvas) {
        canvas.background()
        canvas.text("Lens calibration", in: canvas.rect(VRPanelLayouts.calibrationTitle), size: canvas.height * 0.055, bold: true, color: Ink.text)
        for row in calibration.rows {
            let frame = VRPanelLayouts.calibrationRow(row.parameter)
            let selected = calibration.selected == row.parameter
            if selected {
                canvas.fill(canvas.rect(frame), color: Ink.buttonOn, radius: canvas.rect(frame).height * 0.2)
            }
            let label = VRRect(x: frame.x + 0.02, y: frame.y, width: 0.4, height: frame.height)
            canvas.text(row.parameter.title, in: canvas.rect(label), size: canvas.rect(frame).height * 0.36, color: selected ? Ink.text : Ink.secondary, alignment: .leading)
            let value = VRRect(x: 0.6, y: frame.y, width: 0.23, height: frame.height)
            canvas.text(row.value, in: canvas.rect(value), size: canvas.rect(frame).height * 0.38, bold: true, color: Ink.text)
        }
        for button in VRPanelLayouts.calibrationButtons {
            let r = canvas.rect(button.frame)
            let hovered = calibration.hovered == button.target
            let title: String
            switch button.target {
            case .calibrationStep(_, let direction):
                title = direction < 0 ? "−" : "+"
            case .calibrationDone:
                title = "Done"
            case .menuHub, .menu, .sceneSign:
                continue
            }
            canvas.fill(r, color: hovered ? Ink.buttonHover : Ink.button, radius: r.height * 0.25)
            if hovered { canvas.stroke(r, color: Ink.accent, radius: r.height * 0.25, width: 4) }
            canvas.text(title, in: r, size: r.height * (button.target == .calibrationDone ? 0.36 : 0.6), bold: true, color: Ink.text)
        }
    }

    private func drawStats(_ lines: [String], on canvas: Canvas) {
        canvas.background()
        let rowHeight = 1.0 / Float(max(lines.count, 1))
        for (i, line) in lines.enumerated() {
            let r = VRRect(x: 0.06, y: Float(i) * rowHeight, width: 0.88, height: rowHeight)
            canvas.text(line, in: canvas.rect(r), size: canvas.rect(r).height * 0.52, bold: i == 0, color: i == 0 ? Ink.accent : Ink.text, alignment: .leading)
        }
    }

    private func drawCountdown(_ seconds: Int, subtitle: String, on canvas: Canvas) {
        canvas.background()
        canvas.text("\(seconds)", in: canvas.rect(VRRect(x: 0, y: 0.08, width: 1, height: 0.56)), size: canvas.height * 0.42, bold: true, color: Ink.accent)
        canvas.text(subtitle, in: canvas.rect(VRRect(x: 0.04, y: 0.66, width: 0.92, height: 0.24)), size: canvas.height * 0.1, color: Ink.text)
    }

    private func drawMessage(_ text: String, on canvas: Canvas) {
        canvas.background()
        canvas.text(text, in: canvas.rect(VRRect(x: 0.04, y: 0, width: 0.92, height: 1)), size: canvas.height * 0.36, color: Ink.text)
    }
}

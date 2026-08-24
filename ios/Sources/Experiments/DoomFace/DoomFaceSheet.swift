import CoreGraphics
import CoreImage
import UIKit

/// One cell on the Doom status-bar face sheet.
struct DoomFaceSlot: Hashable, Identifiable {
    /// Health / damage row for the eight shared expressions (`nil` for god + dead).
    let health: Int?
    let expression: DoomFaceExpression

    var id: String {
        if let health {
            return "h\(health)-\(expression.rawValue)"
        }
        return expression.rawValue
    }
}

/// Expression columns on the sheet (plus the two specials).
enum DoomFaceExpression: String, CaseIterable, Hashable {
    case lookLeft
    case lookCenter
    case lookRight
    case turnLeft
    case turnRight
    case ouch
    case evil
    case kill
    case god
    case dead

    /// Columns that repeat once per health row (0…4).
    static let perHealth: [DoomFaceExpression] = [
        .lookLeft, .lookCenter, .lookRight,
        .turnLeft, .turnRight,
        .ouch, .evil, .kill,
    ]

    var isSpecial: Bool {
        self == .god || self == .dead
    }

    var displayName: String {
        switch self {
        case .lookLeft: return "Look left"
        case .lookCenter: return "Look center"
        case .lookRight: return "Look right"
        case .turnLeft: return "Turn left"
        case .turnRight: return "Turn right"
        case .ouch: return "Ouch"
        case .evil: return "Grin"
        case .kill: return "Rampage"
        case .god: return "God mode"
        case .dead: return "Dead"
        }
    }
}

/// Pixel layout of `DoomGuyFaces` (640×396 source art).
enum DoomFaceSheetLayout {
    static let sheetSize = CGSize(width: 640, height: 396)
    static let faceSize = CGSize(width: 52, height: 66)
    static let healthRowCount = 5

    /// Top-left of each health row’s eight expression cells.
    private static let columnXs: [CGFloat] = [81, 149, 207, 265, 323, 379, 437, 495]
    private static let rowYs: [CGFloat] = [18, 91, 163, 235, 308]
    private static let godOrigin = CGPoint(x: 20, y: 163)
    private static let deadOrigin = CGPoint(x: 560, y: 163)

    static var allSlots: [DoomFaceSlot] {
        var slots: [DoomFaceSlot] = []
        for health in 0..<healthRowCount {
            for expression in DoomFaceExpression.perHealth {
                slots.append(DoomFaceSlot(health: health, expression: expression))
            }
        }
        slots.append(DoomFaceSlot(health: nil, expression: .god))
        slots.append(DoomFaceSlot(health: nil, expression: .dead))
        return slots
    }

    static func rect(for slot: DoomFaceSlot) -> CGRect {
        let size = faceSize
        switch slot.expression {
        case .god:
            return CGRect(origin: godOrigin, size: size)
        case .dead:
            return CGRect(origin: deadOrigin, size: size)
        default:
            guard let health = slot.health,
                  health >= 0, health < healthRowCount,
                  let column = DoomFaceExpression.perHealth.firstIndex(of: slot.expression)
            else {
                return .zero
            }
            return CGRect(
                x: columnXs[column],
                y: rowYs[health],
                width: size.width,
                height: size.height
            )
        }
    }

    /// Next empty slot for an expression: top health row first; god/dead are unique.
    static func nextEmptySlot(
        for expression: DoomFaceExpression,
        filled: Set<DoomFaceSlot>
    ) -> DoomFaceSlot? {
        if expression.isSpecial {
            let slot = DoomFaceSlot(health: nil, expression: expression)
            return filled.contains(slot) ? nil : slot
        }
        for health in 0..<healthRowCount {
            let slot = DoomFaceSlot(health: health, expression: expression)
            if !filled.contains(slot) {
                return slot
            }
        }
        return nil
    }
}

/// Builds the live sheet preview (grey originals, color captures stamped in).
enum DoomFaceCompositor {
    static func loadTemplate() -> UIImage? {
        UIImage(named: "DoomGuyFaces")
    }

    /// Greyscale copy of the template so unmatched faces read as locked-in placeholders.
    static func greyscaleTemplate(from template: UIImage) -> UIImage? {
        guard let cgImage = template.cgImage else { return nil }
        let extent = CGRect(origin: .zero, size: CGSize(width: cgImage.width, height: cgImage.height))
        let ciImage = CIImage(cgImage: cgImage).applyingFilter(
            "CIColorControls",
            parameters: [kCIInputSaturationKey: 0]
        ).applyingFilter(
            "CIColorControls",
            parameters: [kCIInputBrightnessKey: -0.08, kCIInputContrastKey: 0.92]
        )
        let context = CIContext(options: [.useSoftwareRenderer: false])
        guard let out = context.createCGImage(ciImage, from: extent) else { return nil }
        return UIImage(cgImage: out, scale: template.scale, orientation: .up)
    }

    /// Stamps captured face crops into their sheet slots over the grey template.
    static func compose(
        greyscaleTemplate: UIImage,
        colorTemplate: UIImage,
        captures: [DoomFaceSlot: UIImage]
    ) -> UIImage? {
        let size = DoomFaceSheetLayout.sheetSize
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        let renderer = UIGraphicsImageRenderer(size: size, format: format)
        return renderer.image { ctx in
            greyscaleTemplate.draw(in: CGRect(origin: .zero, size: size))
            for (slot, face) in captures {
                let rect = DoomFaceSheetLayout.rect(for: slot)
                guard rect.width > 0 else { continue }
                // Punch the original color cell back, then cover with the photo crop.
                if let croppedOriginal = crop(colorTemplate, to: rect) {
                    croppedOriginal.draw(in: rect)
                }
                face.draw(in: rect)
                ctx.cgContext.setStrokeColor(UIColor.white.withAlphaComponent(0.35).cgColor)
                ctx.cgContext.setLineWidth(1)
                ctx.cgContext.stroke(rect.insetBy(dx: 0.5, dy: 0.5))
            }
        }
    }

    static func crop(_ image: UIImage, to rect: CGRect) -> UIImage? {
        guard let cgImage = image.cgImage else { return nil }
        let scaleX = CGFloat(cgImage.width) / image.size.width
        let scaleY = CGFloat(cgImage.height) / image.size.height
        let scaled = CGRect(
            x: rect.origin.x * scaleX,
            y: rect.origin.y * scaleY,
            width: rect.width * scaleX,
            height: rect.height * scaleY
        ).integral
        guard let cut = cgImage.cropping(to: scaled) else { return nil }
        return UIImage(cgImage: cut, scale: 1, orientation: .up)
    }

    /// Scales a camera face crop into the 52×66 doom cell.
    static func fitFace(_ image: UIImage, to cell: CGSize = DoomFaceSheetLayout.faceSize) -> UIImage {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: cell, format: format).image { _ in
            // Aspect-fill into the cell, centered.
            let scale = max(cell.width / image.size.width, cell.height / image.size.height)
            let scaled = CGSize(width: image.size.width * scale, height: image.size.height * scale)
            let origin = CGPoint(
                x: (cell.width - scaled.width) / 2,
                y: (cell.height - scaled.height) / 2
            )
            image.draw(in: CGRect(origin: origin, size: scaled))
        }
    }
}

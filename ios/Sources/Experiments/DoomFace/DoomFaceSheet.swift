import CoreGraphics
import CoreImage
import UIKit

struct DoomFaceSlot: Hashable, Identifiable {
    /// Health row 0…4, or `nil` for god / dead.
    let health: Int?
    let expression: DoomFaceExpression

    var id: String {
        if let health {
            return "h\(health)-\(expression.rawValue)"
        }
        return expression.rawValue
    }
}

enum DoomFaceExpression: String, CaseIterable, Hashable {
    case lookLeft, lookCenter, lookRight
    case turnLeft, turnRight
    case ouch, evil, kill
    case god, dead

    static let perHealth: [DoomFaceExpression] = [
        .lookLeft, .lookCenter, .lookRight,
        .turnLeft, .turnRight,
        .ouch, .evil, .kill,
    ]

    var isSpecial: Bool { self == .god || self == .dead }

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

/// Pixel layout of the bundled `DoomGuyFaces` image (640×396).
enum DoomFaceSheetLayout {
    static let sheetSize = CGSize(width: 640, height: 396)
    static let faceSize = CGSize(width: 52, height: 66)
    static let healthRowCount = 5

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
        switch slot.expression {
        case .god:
            return CGRect(origin: godOrigin, size: faceSize)
        case .dead:
            return CGRect(origin: deadOrigin, size: faceSize)
        default:
            guard let health = slot.health,
                  (0..<healthRowCount).contains(health),
                  let column = DoomFaceExpression.perHealth.firstIndex(of: slot.expression)
            else {
                return .zero
            }
            return CGRect(
                x: columnXs[column],
                y: rowYs[health],
                width: faceSize.width,
                height: faceSize.height
            )
        }
    }

    /// Next empty cell for an expression (top health row first).
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
            if !filled.contains(slot) { return slot }
        }
        return nil
    }
}

enum DoomFaceCompositor {
    static func loadTemplate() -> UIImage? {
        UIImage(named: "DoomGuyFaces")
    }

    static func greyscaleTemplate(from template: UIImage) -> UIImage? {
        guard let cgImage = template.cgImage else { return nil }
        let extent = CGRect(origin: .zero, size: CGSize(width: cgImage.width, height: cgImage.height))
        let mono = CIImage(cgImage: cgImage).applyingFilter(
            "CIColorControls",
            parameters: [kCIInputSaturationKey: 0]
        )
        let context = CIContext(options: [.useSoftwareRenderer: false])
        guard let out = context.createCGImage(mono, from: extent) else { return nil }
        return UIImage(cgImage: out, scale: template.scale, orientation: .up)
    }

    static func compose(
        greyscaleTemplate: UIImage,
        captures: [DoomFaceSlot: UIImage]
    ) -> UIImage {
        let size = DoomFaceSheetLayout.sheetSize
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: size, format: format).image { _ in
            greyscaleTemplate.draw(in: CGRect(origin: .zero, size: size))
            for (slot, face) in captures {
                let rect = DoomFaceSheetLayout.rect(for: slot)
                guard rect.width > 0 else { continue }
                face.draw(in: rect)
            }
        }
    }

    static func fitFace(_ image: UIImage, to cell: CGSize = DoomFaceSheetLayout.faceSize) -> UIImage {
        let format = UIGraphicsImageRendererFormat.default()
        format.scale = 1
        format.opaque = true
        return UIGraphicsImageRenderer(size: cell, format: format).image { _ in
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

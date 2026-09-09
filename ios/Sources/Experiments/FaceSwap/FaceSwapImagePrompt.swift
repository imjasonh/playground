import Foundation
import UIKit

enum FaceSwapImageError: LocalizedError, Equatable {
    case imageInputUnavailable
    case missingEditPlan

    var errorDescription: String? {
        switch self {
        case .imageInputUnavailable:
            return "Face Swap needs the on-device model on iOS 26 or later."
        case .missingEditPlan:
            return "The model did not choose an edit. No pixels changed."
        }
    }
}

/// Image attachments exist on the iOS 27 on-device model. Older SDKs compile
/// without that type, and the experiment refuses to invent outlines instead.
enum FaceSwapImagePromptSupport {
    static var canAttachImages: Bool {
        #if compiler(>=6.3) && canImport(FoundationModels)
        if #available(iOS 27.0, *) {
            return true
        }
        #endif
        return false
    }
}

enum FaceSwapImagePrompt {
    static let previewLongEdge = 512
    /// Attached preview is smaller than the working copy so it fits the 4096-token window.
    static let modelPreviewLongEdge = 256
    static let cropLongEdge = 256

    static func previewImage(from raster: FaceSwapRaster, maxEdge: Int = previewLongEdge) -> UIImage? {
        guard let decoded = FaceSwapRaster.decode(raster.uiImage() ?? UIImage(), maxEdge: maxEdge) else {
            return raster.uiImage()
        }
        return decoded.raster.uiImage()
    }

    static func crop(_ raster: FaceSwapRaster, outline: FaceSwapOutline, padding: CGFloat) -> UIImage? {
        let bounds = FaceSwapOutlineValidation.boundsOf(outline.points)
        let padX = bounds.width * padding
        let padY = bounds.height * padding
        let normalized = CGRect(
            x: bounds.minX - padX,
            y: bounds.minY - padY,
            width: bounds.width + padX * 2,
            height: bounds.height + padY * 2
        )
        let pixel = CGRect(
            x: normalized.minX * CGFloat(raster.width),
            y: normalized.minY * CGFloat(raster.height),
            width: normalized.width * CGFloat(raster.width),
            height: normalized.height * CGFloat(raster.height)
        ).intersection(CGRect(x: 0, y: 0, width: raster.width, height: raster.height))
        let minX = max(0, Int(pixel.minX.rounded(.down)))
        let minY = max(0, Int(pixel.minY.rounded(.down)))
        let maxX = min(raster.width, Int(pixel.maxX.rounded(.up)))
        let maxY = min(raster.height, Int(pixel.maxY.rounded(.up)))
        let width = maxX - minX
        let height = maxY - minY
        guard width >= 8, height >= 8 else { return nil }
        var cropped = FaceSwapRaster.solid(width: width, height: height, red: 0, green: 0, blue: 0)
        for y in 0..<height {
            for x in 0..<width {
                guard let color = raster.rgb(x: minX + x, y: minY + y) else { continue }
                cropped.setRGB(x: x, y: y, red: color.0, green: color.1, blue: color.2)
            }
        }
        guard let image = cropped.uiImage() else { return nil }
        return FaceSwapRaster.decode(image, maxEdge: cropLongEdge)?.raster.uiImage() ?? image
    }
}

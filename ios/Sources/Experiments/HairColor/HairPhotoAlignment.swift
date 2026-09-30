import CoreImage
import ImageIO

/// Still-photo hair mattes share the sensor buffer's orientation. `CIImage(data:)`
/// already applies EXIF, so the matte has to be turned to match that upright photo.
/// If the turned matte's aspect is farther from the photo than the raw matte, keep
/// the raw matte. That happens when the buffer was already upright.
enum HairPhotoAlignment {
    static func orientation(from metadata: [String: Any]) -> CGImagePropertyOrientation {
        let value = metadata[kCGImagePropertyOrientation as String]
        let raw: UInt32
        if let number = value as? UInt32 {
            raw = number
        } else if let number = value as? Int {
            raw = UInt32(clamping: number)
        } else if let number = value as? NSNumber {
            raw = number.uint32Value
        } else {
            raw = 1
        }
        return CGImagePropertyOrientation(rawValue: raw) ?? .up
    }

    static func matching(
        _ matte: CIImage,
        to image: CIImage,
        orientation: CGImagePropertyOrientation
    ) -> CIImage {
        let raw = HairColorOrientation.rebase(matte)
        let turned = HairColorOrientation.rebase(matte.oriented(orientation))
        let target = aspect(image.extent)
        if abs(aspect(turned.extent) - target) <= abs(aspect(raw.extent) - target) {
            return turned
        }
        return raw
    }

    private static func aspect(_ extent: CGRect) -> CGFloat {
        guard extent.width.isFinite, extent.height.isFinite, extent.height > 0 else { return 1 }
        return extent.width / extent.height
    }
}

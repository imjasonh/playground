import CoreImage
import CoreVideo
import UIKit

/// Dyes hair pixels in place. `CIColorBlendMode` takes hue from the dye and
/// luminance from the camera pixel, then `CIBlendWithMask` limits that to the mask.
enum HairColorCompositor {
    static func apply(
        image: CIImage,
        mask: CIImage,
        dye: HairDye,
        strength: CGFloat,
        blurRadius: CGFloat
    ) -> CIImage {
        let extent = image.extent
        guard extent.width.isFinite, extent.height.isFinite, extent.width > 1, extent.height > 1 else {
            return image
        }
        let amount = min(max(strength, 0), 1)
        guard amount > 0 else { return image }

        let scaledMask = scale(mask, to: extent)
        guard let weighted = multiply(scaledMask, by: amount)?.cropped(to: extent) else {
            return image
        }
        let softened = blur(weighted, radius: blurRadius, extent: extent)

        let colorImage = CIImage(color: dye.ciColor).cropped(to: extent)
        guard let tinted = colorBlend(color: colorImage, background: image)?.cropped(to: extent) else {
            return image
        }
        guard let blended = blend(foreground: tinted, background: image, mask: softened) else {
            return image
        }
        return blended.cropped(to: extent)
    }

    /// Paints the mask in rose so you can see which pixels the dye would touch.
    static func showMask(image: CIImage, mask: CIImage) -> CIImage {
        let extent = image.extent
        guard extent.width.isFinite, extent.height.isFinite else { return image }
        let scaled = scale(mask, to: extent)
        let rose = CIImage(color: CIColor(red: 1, green: 0.25, blue: 0.45, alpha: 1)).cropped(to: extent)
        guard let over = blend(foreground: rose, background: image, mask: scaled) else {
            return image
        }
        return over.cropped(to: extent)
    }

    static func render(_ image: CIImage, context: CIContext) -> UIImage? {
        let extent = image.extent.integral
        guard extent.width.isFinite, extent.height.isFinite, extent.width > 1, extent.height > 1 else {
            return nil
        }
        guard let cgImage = context.createCGImage(image, from: extent) else { return nil }
        return UIImage(cgImage: cgImage)
    }

    private static func scale(_ mask: CIImage, to extent: CGRect) -> CIImage {
        let maskExtent = mask.extent
        guard maskExtent.width.isFinite, maskExtent.height.isFinite,
              maskExtent.width > 0, maskExtent.height > 0 else {
            return mask.cropped(to: extent)
        }
        let scaleX = extent.width / maskExtent.width
        let scaleY = extent.height / maskExtent.height
        let scaled = mask.transformed(by: CGAffineTransform(scaleX: scaleX, y: scaleY))
        return HairColorOrientation.rebase(scaled).cropped(to: extent)
    }

    private static func multiply(_ image: CIImage, by amount: CGFloat) -> CIImage? {
        guard let filter = CIFilter(name: "CIColorMatrix") else { return nil }
        filter.setValue(image, forKey: kCIInputImageKey)
        filter.setValue(CIVector(x: amount, y: 0, z: 0, w: 0), forKey: "inputRVector")
        filter.setValue(CIVector(x: 0, y: amount, z: 0, w: 0), forKey: "inputGVector")
        filter.setValue(CIVector(x: 0, y: 0, z: amount, w: 0), forKey: "inputBVector")
        filter.setValue(CIVector(x: 0, y: 0, z: 0, w: amount), forKey: "inputAVector")
        filter.setValue(CIVector(x: 0, y: 0, z: 0, w: 0), forKey: "inputBiasVector")
        return filter.outputImage
    }

    private static func blur(_ image: CIImage, radius: CGFloat, extent: CGRect) -> CIImage {
        guard radius > 0.5, let filter = CIFilter(name: "CIGaussianBlur") else {
            return image.cropped(to: extent)
        }
        filter.setValue(image, forKey: kCIInputImageKey)
        filter.setValue(radius, forKey: kCIInputRadiusKey)
        return (filter.outputImage ?? image).cropped(to: extent)
    }

    private static func colorBlend(color: CIImage, background: CIImage) -> CIImage? {
        guard let filter = CIFilter(name: "CIColorBlendMode") else { return nil }
        filter.setValue(color, forKey: kCIInputImageKey)
        filter.setValue(background, forKey: kCIInputBackgroundImageKey)
        return filter.outputImage
    }

    private static func blend(foreground: CIImage, background: CIImage, mask: CIImage) -> CIImage? {
        guard let filter = CIFilter(name: "CIBlendWithMask") else { return nil }
        filter.setValue(foreground, forKey: kCIInputImageKey)
        filter.setValue(background, forKey: kCIInputBackgroundImageKey)
        filter.setValue(mask, forKey: kCIInputMaskImageKey)
        return filter.outputImage
    }
}

enum HairMaskImage {
    /// Owns a private copy of a single-plane matte so the photo callback can return.
    static func detached(_ buffer: CVPixelBuffer) -> CVPixelBuffer? {
        guard CVPixelBufferIsPlanar(buffer) == false else { return nil }
        let width = CVPixelBufferGetWidth(buffer)
        let height = CVPixelBufferGetHeight(buffer)
        guard width > 0, height > 0 else { return nil }
        var copy: CVPixelBuffer?
        let status = CVPixelBufferCreate(
            kCFAllocatorDefault,
            width,
            height,
            CVPixelBufferGetPixelFormatType(buffer),
            nil,
            &copy
        )
        guard status == kCVReturnSuccess, let copy else { return nil }
        let sourceStatus = CVPixelBufferLockBaseAddress(buffer, .readOnly)
        let copyStatus = CVPixelBufferLockBaseAddress(copy, [])
        defer {
            if copyStatus == kCVReturnSuccess {
                CVPixelBufferUnlockBaseAddress(copy, [])
            }
            if sourceStatus == kCVReturnSuccess {
                CVPixelBufferUnlockBaseAddress(buffer, .readOnly)
            }
        }
        guard sourceStatus == kCVReturnSuccess, copyStatus == kCVReturnSuccess,
              let source = CVPixelBufferGetBaseAddress(buffer),
              let destination = CVPixelBufferGetBaseAddress(copy) else { return nil }
        let sourceRow = CVPixelBufferGetBytesPerRow(buffer)
        let destinationRow = CVPixelBufferGetBytesPerRow(copy)
        let row = min(sourceRow, destinationRow)
        for y in 0..<height {
            memcpy(destination.advanced(by: y * destinationRow), source.advanced(by: y * sourceRow), row)
        }
        return copy
    }

    /// Copies a packed grayscale buffer into a mask `CIImage`. Row 0 is the top.
    static func make(bytes: [UInt8], width: Int, height: Int) -> CIImage? {
        guard width > 0, height > 0, bytes.count == width * height else { return nil }
        let attributes: [CFString: Any] = [
            kCVPixelBufferCGImageCompatibilityKey: true,
            kCVPixelBufferCGBitmapContextCompatibilityKey: true,
        ]
        var buffer: CVPixelBuffer?
        let status = CVPixelBufferCreate(
            kCFAllocatorDefault,
            width,
            height,
            kCVPixelFormatType_OneComponent8,
            attributes as CFDictionary,
            &buffer
        )
        guard status == kCVReturnSuccess, let buffer else { return nil }
        CVPixelBufferLockBaseAddress(buffer, [])
        defer { CVPixelBufferUnlockBaseAddress(buffer, []) }
        guard let base = CVPixelBufferGetBaseAddress(buffer) else { return nil }
        let rowBytes = CVPixelBufferGetBytesPerRow(buffer)
        bytes.withUnsafeBytes { raw in
            guard let source = raw.baseAddress else { return }
            for y in 0..<height {
                let destination = base.advanced(by: y * rowBytes)
                memcpy(destination, source.advanced(by: y * width), width)
            }
        }
        return CIImage(cvPixelBuffer: buffer)
    }
}

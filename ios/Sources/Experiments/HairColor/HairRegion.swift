import CoreGraphics
import Vision

/// Where hair can be, in Vision-normalized coordinates (origin at the bottom left).
///
/// `VNGeneratePersonSegmentationRequest` covers the whole person. Live video does
/// not receive `AVSemanticSegmentationMatte.hair` (that matte is a still-photo
/// attachment). The live mask is the person matte restricted to this region so
/// the dye stays off the face, clothes, and background.
struct HairRegion: Equatable {
    var window: CGRect
    /// Pixels at or above this Y, inside `window`, are the crown.
    var hairlineY: CGFloat
    /// Face skin below the forehead. Excluded from the mask.
    var faceInterior: CGRect
    /// Sideburns stop at this Y. Lower pixels are neck and shoulders.
    var sideburnMinY: CGFloat
    /// Bottom of the forehead. Skin from here up to `hairlineY`, across the face width, is not hair.
    var foreheadMinY: CGFloat?
    /// Face box edges. The forehead exclusion uses the full width, not the inset interior.
    var faceMinX: CGFloat
    var faceMaxX: CGFloat

    func contains(x: CGFloat, y: CGFloat) -> Bool {
        let point = CGPoint(x: x, y: y)
        guard window.contains(point) else { return false }
        if y >= hairlineY { return true }
        if y < sideburnMinY { return false }
        if let foreheadMinY, y >= foreheadMinY, x >= faceMinX, x <= faceMaxX {
            return false
        }
        if faceInterior.contains(point) { return false }
        return true
    }
}

/// A detected face, plus an optional eyebrow line in the same normalized space.
struct FaceHairGuide: Equatable {
    var boundingBox: CGRect
    /// Image-normalized eyebrow line. The hairline stays at the top of the box.
    var eyebrowY: CGFloat?
}

enum HairRegionBuilder {
    /// How far below the top of the face box the scalp still counts, relative to face height.
    /// Kept small so the forehead under the hairline stays out of the dye.
    static let hairlineInset: CGFloat = 0.02
    /// How far the crown extends above the face box, relative to face height.
    static let crownScale: CGFloat = 0.90
    /// Horizontal padding on each side of the face, relative to face width.
    static let sideScale: CGFloat = 0.40
    /// How far sideburns hang below the eyebrows, relative to face height.
    static let sideburnScale: CGFloat = 0.22
    /// Inset of the excluded face oval from the face box, relative to face width.
    static let faceInsetScale: CGFloat = 0.08

    static func region(for face: FaceHairGuide) -> HairRegion? {
        let box = face.boundingBox.standardized
        guard box.width > 0.02, box.height > 0.02 else { return nil }

        // Eyebrows sit well below the hairline. Using them as the hairline dyes the forehead.
        let hairline = box.maxY - (box.height * hairlineInset)
        let eyebrow = face.eyebrowY.map { min(max($0, box.minY), box.maxY) }
        let foreheadMinY: CGFloat? = eyebrow.flatMap { brow in
            brow < hairline ? brow : nil
        }

        let side = box.width * sideScale
        let sideburnDrop = box.height * sideburnScale
        let inset = box.width * faceInsetScale
        let crownTop = box.maxY + (box.height * crownScale)
        let sideburnAnchor = foreheadMinY ?? hairline
        let sideburnBottom = sideburnAnchor - sideburnDrop
        let interiorTop = foreheadMinY ?? hairline
        let interiorWidth = max(0, box.width - (inset * 2))
        let interiorHeight = max(0, interiorTop - box.minY)

        return HairRegion(
            window: CGRect(
                x: box.minX - side,
                y: sideburnBottom,
                width: box.width + (side * 2),
                height: crownTop - sideburnBottom
            ),
            hairlineY: hairline,
            faceInterior: CGRect(
                x: box.minX + inset,
                y: box.minY,
                width: interiorWidth,
                height: interiorHeight
            ),
            sideburnMinY: sideburnBottom,
            foreheadMinY: foreheadMinY,
            faceMinX: box.minX,
            faceMaxX: box.maxX
        )
    }

    static func regions(for faces: [FaceHairGuide]) -> [HairRegion] {
        faces.compactMap { region(for: $0) }
    }
}

enum HairFaceGuideBuilder {
    /// Maps one landmark Y (normalized inside the face box) into image-normalized Y.
    static func imageNormalizedY(landmarkY: CGFloat, box: CGRect) -> CGFloat {
        box.minY + (landmarkY * box.height)
    }

    static func averageEyebrowY(landmarkYs: [CGFloat], box: CGRect) -> CGFloat? {
        guard !landmarkYs.isEmpty else { return nil }
        let sum = landmarkYs.reduce(CGFloat(0)) { partial, landmarkY in
            partial + imageNormalizedY(landmarkY: landmarkY, box: box)
        }
        return sum / CGFloat(landmarkYs.count)
    }

    static func guides(from faces: [VNFaceObservation]) -> [FaceHairGuide] {
        faces.map { face in
            let box = face.boundingBox
            let eyebrows = eyebrowLandmarkYs(in: face)
            return FaceHairGuide(
                boundingBox: box,
                eyebrowY: averageEyebrowY(landmarkYs: eyebrows, box: box)
            )
        }
    }

    private static func eyebrowLandmarkYs(in face: VNFaceObservation) -> [CGFloat] {
        guard let landmarks = face.landmarks else { return [] }
        let points = (landmarks.leftEyebrow?.normalizedPoints ?? [])
            + (landmarks.rightEyebrow?.normalizedPoints ?? [])
        return points.map(\.y)
    }
}

/// Grayscale person matte, row 0 at the top, multiplied by the hair regions.
enum HairMaskRasterizer {
    static func maskBytes(
        person: [UInt8],
        width: Int,
        height: Int,
        regions: [HairRegion]
    ) -> [UInt8] {
        guard width > 0, height > 0, person.count == width * height else { return [] }
        var output = [UInt8](repeating: 0, count: person.count)
        guard !regions.isEmpty else { return output }

        for y in 0..<height {
            for x in 0..<width {
                let nx = (CGFloat(x) + 0.5) / CGFloat(width)
                let ny = 1 - ((CGFloat(y) + 0.5) / CGFloat(height))
                let isHair = regions.contains { $0.contains(x: nx, y: ny) }
                guard isHair else { continue }
                let index = (y * width) + x
                output[index] = person[index]
            }
        }
        return output
    }
}

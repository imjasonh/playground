import CoreGraphics
import Vision

/// Sampling and exclusion rectangles for one face, in Vision coordinates (origin at the bottom left).
///
/// Live video does not include `AVSemanticSegmentationMatte.hair`. These rectangles
/// tell the color matcher where to sample hair, where to sample skin, and which
/// pixels belong to the face.
struct HairRegion: Equatable {
    /// Person pixels above the face box. Their color is the hair sample, and they seed the mask.
    var crown: CGRect
    /// Cheek pixels used as the skin sample.
    var skinSample: CGRect
    /// Face from the chin up to the eyebrows. These pixels are never dyed.
    var protected: CGRect
    /// Torso pixels used to recognize clothes that should stay undyed.
    var clothesSample: CGRect
    /// Where connected hair may extend, including bangs and long hair.
    var search: CGRect
}

/// A detected face, plus an optional eyebrow line in the same normalized space.
struct FaceHairGuide: Equatable {
    var boundingBox: CGRect
    /// Image-normalized eyebrow line. The hairline stays at the top of the box.
    var eyebrowY: CGFloat?
}

enum HairRegionBuilder {
    /// How far the crown sample extends above the face box, relative to face height.
    static let crownScale: CGFloat = 0.90
    /// Horizontal padding on the crown sample, relative to face width.
    static let crownSideScale: CGFloat = 0.35
    /// How far the search extends past each side of the face, relative to face width.
    static let searchSideScale: CGFloat = 1.6
    /// How far below the chin the search continues, relative to face height.
    static let searchDropScale: CGFloat = 3
    /// Without eyebrows, protect the lower portion of the face box.
    static let fallbackProtectedFraction: CGFloat = 0.72

    static func region(for face: FaceHairGuide) -> HairRegion? {
        let box = face.boundingBox.standardized
        guard box.width > 0.02, box.height > 0.02 else { return nil }

        let protectedTop: CGFloat
        if let eyebrow = face.eyebrowY {
            protectedTop = min(max(eyebrow, box.minY), box.maxY)
        } else {
            protectedTop = box.minY + (box.height * fallbackProtectedFraction)
        }

        let crownTop = min(1, box.maxY + (box.height * crownScale))
        let side = box.width * crownSideScale
        let skinBottom = box.minY + ((protectedTop - box.minY) * 0.45)
        let clothesHeight = box.height * 0.45
        let clothesTop = box.minY - (box.height * 0.35)
        let searchBottom = max(0, box.minY - (box.height * searchDropScale))

        return HairRegion(
            crown: CGRect(
                x: box.minX - side,
                y: box.maxY,
                width: box.width + (side * 2),
                height: max(0, crownTop - box.maxY)
            ),
            skinSample: CGRect(
                x: box.minX + (box.width * 0.30),
                y: skinBottom,
                width: box.width * 0.40,
                height: max(0, protectedTop - skinBottom)
            ),
            protected: CGRect(
                x: box.minX,
                y: box.minY,
                width: box.width,
                height: max(0, protectedTop - box.minY)
            ),
            clothesSample: CGRect(
                x: box.minX + (box.width * 0.25),
                y: clothesTop - clothesHeight,
                width: box.width * 0.50,
                height: clothesHeight
            ),
            search: CGRect(
                x: box.minX - (box.width * searchSideScale),
                y: searchBottom,
                width: box.width * ((searchSideScale * 2) + 1),
                height: max(0, crownTop - searchBottom)
            )
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

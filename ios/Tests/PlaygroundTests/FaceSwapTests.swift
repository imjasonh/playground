import CoreGraphics
import UIKit
import XCTest
@testable import Playground

final class FaceSwapTests: XCTestCase {
    func testPrepareAcceptsTwoFaceContours() {
        let pair = facePair()
        switch FaceSwapOutlineValidation.prepare([pair.source, pair.destination]) {
        case .success(let prepared):
            XCTAssertEqual(prepared.source.role, .source)
            XCTAssertEqual(prepared.destination.role, .destination)
            XCTAssertEqual(prepared.source.refersTo, "the man's face")
        case .failure(let error):
            XCTFail(error.message)
        }
    }

    func testPrepareRejectsBoxHairAndFullFrameOutlines() {
        var box = facePair().source
        box.points = [
            CGPoint(x: 0.20, y: 0.20),
            CGPoint(x: 0.30, y: 0.20),
            CGPoint(x: 0.40, y: 0.20),
            CGPoint(x: 0.40, y: 0.35),
            CGPoint(x: 0.40, y: 0.50),
            CGPoint(x: 0.30, y: 0.50),
            CGPoint(x: 0.20, y: 0.50),
            CGPoint(x: 0.20, y: 0.35),
        ]
        XCTAssertTrue(FaceSwapOutlineValidation.check(box)?.contains("box") == true)

        var wide = facePair().destination
        wide.points = contour(center: CGPoint(x: 0.5, y: 0.5), radiusX: 0.30, radiusY: 0.16)
        XCTAssertTrue(FaceSwapOutlineValidation.check(wide)?.contains("too wide") == true)

        var frame = facePair().destination
        frame.points = contour(center: CGPoint(x: 0.5, y: 0.5), radiusX: 0.48, radiusY: 0.48)
        XCTAssertNotNil(FaceSwapOutlineValidation.check(frame))
    }

    func testTighteningCannotGrowPastTracedOutline() {
        let destination = facePair().destination
        let inside = contour(
            center: CGPoint(x: 0.70, y: 0.50),
            radiusX: 0.06,
            radiusY: 0.08
        )
        XCTAssertNotNil(FaceSwapOutlineValidation.acceptedTightening(base: destination.points, tightened: inside))

        let outside = contour(
            center: CGPoint(x: 0.70, y: 0.50),
            radiusX: 0.16,
            radiusY: 0.20
        )
        XCTAssertNil(FaceSwapOutlineValidation.acceptedTightening(base: destination.points, tightened: outside))
    }

    func testClosedJawIsAFaceContour() {
        let jaw = [
            CGPoint(x: 0.20, y: 0.42),
            CGPoint(x: 0.24, y: 0.55),
            CGPoint(x: 0.32, y: 0.62),
            CGPoint(x: 0.40, y: 0.55),
            CGPoint(x: 0.44, y: 0.42),
        ]
        let closed = FaceSwapContours.closeJaw(
            jaw,
            brows: [CGPoint(x: 0.24, y: 0.34), CGPoint(x: 0.40, y: 0.34)]
        )
        XCTAssertGreaterThan(closed.count, jaw.count)
        XCTAssertTrue(closed.contains { $0.y < 0.34 })
        let outline = FaceSwapOutline(id: "face-1", role: .source, refersTo: "left face", points: closed)
        XCTAssertNil(FaceSwapOutlineValidation.check(outline))
    }

    func testReconstructionStaysInsideOutlineAndIsNotAStamp() throws {
        let size = 96
        var photo = FaceSwapRaster.solid(width: size, height: size, red: 20, green: 120, blue: 40)
        let pair = facePair()
        paint(&photo, outline: pair.source, red: 220, green: 180, blue: 40)
        paint(&photo, outline: pair.destination, red: 40, green: 50, blue: 90)
        let original = photo

        let reconstructed = try XCTUnwrap(apply(
            plan: recipe(lightingMatch: 1, colorMatch: 0, detailTransfer: 0),
            pair: pair,
            photo: photo
        ))
        let stamped = try XCTUnwrap(apply(
            plan: recipe(lightingMatch: 0, colorMatch: 0, detailTransfer: 0),
            pair: pair,
            photo: photo
        ))

        XCTAssertEqual(reconstructed.stats.outsideMaskChanged, 0)
        XCTAssertEqual(stamped.stats.outsideMaskChanged, 0)
        XCTAssertLessThan(reconstructed.stats.percentChanged, 22)
        assertUnchangedOutside(original: original, edited: reconstructed.image, outline: pair.destination)

        let interior = interiorLuma(of: reconstructed.image, outline: pair.destination)
        let stampLuma = interiorLuma(of: stamped.image, outline: pair.destination)
        XCTAssertGreaterThan(interior.count, 8)
        XCTAssertLessThan(interior.luma, 110)
        XCTAssertGreaterThan(stampLuma.luma, 115)
        XCTAssertNotEqual(reconstructed.image.rgba, stamped.image.rgba)

        let changed = FaceSwapDiff.changedPixelCount(original: original, edited: reconstructed.image)
        XCTAssertGreaterThan(changed, 0)
        XCTAssertEqual(changed, reconstructed.stats.changedFromOriginal)
        XCTAssertTrue(FaceSwapDiff.summary(original: original, edited: reconstructed.image).contains("Changed"))
    }

    func testFaceTransferKeepsSourceFeaturesAndAlignsEyes() throws {
        let size = 96
        var photo = FaceSwapRaster.solid(width: size, height: size, red: 20, green: 120, blue: 40)
        let pair = facePair()
        paint(&photo, outline: pair.source, red: 210, green: 170, blue: 120)
        paint(&photo, outline: pair.destination, red: 40, green: 50, blue: 90)
        let sourceCenter = CGPoint(x: 0.28 * CGFloat(size), y: 0.42 * CGFloat(size))
        let destCenter = CGPoint(x: 0.70 * CGFloat(size), y: 0.50 * CGFloat(size))
        let sourceLeftEye = CGPoint(x: sourceCenter.x - 8, y: sourceCenter.y - 6)
        let sourceRightEye = CGPoint(x: sourceCenter.x + 8, y: sourceCenter.y - 6)
        let sourceMouth = CGPoint(x: sourceCenter.x, y: sourceCenter.y + 10)
        let destLeftEye = CGPoint(x: destCenter.x - 8, y: destCenter.y - 6)
        let destRightEye = CGPoint(x: destCenter.x + 8, y: destCenter.y - 6)
        let destMouth = CGPoint(x: destCenter.x, y: destCenter.y + 10)
        paintEye(&photo, at: sourceLeftEye, red: 20, green: 20, blue: 20)
        paintEye(&photo, at: sourceRightEye, red: 20, green: 20, blue: 20)

        var plan = recipe(lightingMatch: 0.4, colorMatch: 0, detailTransfer: 1)
        plan.fitPose = 1
        let transferred = try XCTUnwrap(apply(
            plan: plan,
            pair: pair,
            photo: photo,
            sourceLandmarks: FaceSwapLandmarkTrio(leftEye: sourceLeftEye, rightEye: sourceRightEye, mouth: sourceMouth),
            destinationLandmarks: FaceSwapLandmarkTrio(leftEye: destLeftEye, rightEye: destRightEye, mouth: destMouth)
        ))

        let destEye = transferred.image.rgb(x: Int(destLeftEye.x), y: Int(destLeftEye.y))
        let destCheek = transferred.image.rgb(x: Int(destCenter.x), y: Int(destCenter.y))
        XCTAssertLessThan(Int(destEye?.0 ?? 255), Int(destCheek?.0 ?? 0))
        XCTAssertEqual(transferred.stats.outsideMaskChanged, 0)
        XCTAssertEqual(transferred.stats.warp, "eyes")
    }

    func testRemoveAndCopyStayInsideTheirRegions() throws {
        let size = 48
        var photo = FaceSwapRaster.solid(width: size, height: size, red: 20, green: 140, blue: 40)
        let sourceMask = maskRect(x: 4, y: 8, width: 10, height: 12, imageWidth: size, imageHeight: size)
        paint(&photo, mask: sourceMask, red: 30, green: 70, blue: 190)
        let person = region(id: "person-1", kind: .person, colorName: "blue", mask: sourceMask, size: size)

        var face = faceRegion(FaceSwapOutline(
            id: "face-1",
            role: .source,
            refersTo: "",
            points: contour(center: CGPoint(x: 0.18, y: 0.22), radiusX: 0.06, radiusY: 0.08)
        ))
        face.onID = "person-1"
        let catalog = FaceSwapRegions.catalog([person, face])
        XCTAssertTrue(catalog.contains("kind=person"))
        XCTAssertTrue(catalog.contains("color=blue"))
        XCTAssertTrue(catalog.contains("on=person-1 clothing=blue"))
        XCTAssertTrue(catalog.contains("cannot grow"))
        XCTAssertEqual(FaceSwapRegions.colorName(sample: (30, 70, 190)), "blue")
        XCTAssertLessThanOrEqual(FaceSwapRegions.catalog([person, face], maxChars: 48).count, 48)

        let removed = try XCTUnwrap(applyScript([.remove(regionID: "person-1", inset: 0)], regions: [person], photo: photo))
        XCTAssertEqual(removed.stats.outsideMaskChanged, 0)
        assertUnchanged(original: photo, edited: removed.image, outside: sourceMask)
        let hole = removed.image.rgb(x: 8, y: 12)
        XCTAssertGreaterThan(Int(hole?.1 ?? 0), Int(hole?.2 ?? 255))

        let copied = try XCTUnwrap(applyScript(
            [.copy(sourceID: "person-1", centers: [CGPoint(x: 0.75, y: 0.55)])],
            regions: [person],
            photo: photo
        ))
        XCTAssertEqual(copied.stats.outsideMaskChanged, 0)
        XCTAssertEqual(photo.rgb(x: 8, y: 12)?.2, copied.image.rgb(x: 8, y: 12)?.2)
        XCTAssertEqual(copied.image.rgb(x: 1, y: 1)?.1, photo.rgb(x: 1, y: 1)?.1)
        XCTAssertGreaterThan(copied.stats.changedFromOriginal, 0)
        XCTAssertLessThan(copied.stats.percentChanged, 75)

        let huge = [UInt8](repeating: 255, count: size * size)
        let tooBig = region(id: "person-9", kind: .person, colorName: "blue", mask: huge, size: size)
        XCTAssertNotNil(FaceSwapOperations.validate(.remove(regionID: "person-9", inset: 0), regions: [tooBig], width: size, height: size))

        var boxed = person
        boxed.mask = nil
        XCTAssertTrue(
            FaceSwapOperations.validate(.remove(regionID: "person-1", inset: 0), regions: [boxed], width: size, height: size)?
                .contains("rectangle") == true
        )
        XCTAssertTrue(
            FaceSwapOperations.validate(.copy(sourceID: "person-1", centers: [CGPoint(x: 0.7, y: 0.7)]), regions: [boxed], width: size, height: size)?
                .contains("rectangle") == true
        )
    }

    func testFaceSwapRequestDoesNotAlsoCopyOrErase() {
        let faces = [
            faceRegion(FaceSwapOutline(id: "face-1", role: .source, refersTo: "", points: contour(center: CGPoint(x: 0.3, y: 0.4), radiusX: 0.08, radiusY: 0.1))),
            faceRegion(FaceSwapOutline(id: "face-2", role: .destination, refersTo: "", points: contour(center: CGPoint(x: 0.7, y: 0.4), radiusX: 0.08, radiusY: 0.1))),
            faceRegion(FaceSwapOutline(id: "face-3", role: .destination, refersTo: "", points: contour(center: CGPoint(x: 0.5, y: 0.8), radiusX: 0.08, radiusY: 0.1))),
        ]
        let kept = FaceSwapCommandPolicy.select(
            [
                .replaceFaces(sourceID: "face-2", destinationIDs: ["face-1", "face-3"], plan: .identity),
                .copy(sourceID: "person-1", centers: [CGPoint(x: 0.2, y: 0.2), CGPoint(x: 0.8, y: 0.2)]),
            ],
            request: "Swap the man's face onto the woman's body",
            regions: faces
        )
        XCTAssertEqual(kept.count, 1)
        guard case .replaceFaces(let sourceID, let destinationIDs, _) = kept[0] else {
            return XCTFail("Expected a face replacement")
        }
        XCTAssertEqual(sourceID, "face-2")
        XCTAssertEqual(destinationIDs, ["face-1"])
    }

    func testSwapFacesExchangesTwoFacesInsteadOfRemovingThem() {
        let faces = [
            faceRegion(FaceSwapOutline(id: "face-1", role: .source, refersTo: "", points: contour(center: CGPoint(x: 0.3, y: 0.4), radiusX: 0.08, radiusY: 0.1))),
            faceRegion(FaceSwapOutline(id: "face-2", role: .destination, refersTo: "", points: contour(center: CGPoint(x: 0.7, y: 0.4), radiusX: 0.08, radiusY: 0.1))),
        ]
        let kept = FaceSwapCommandPolicy.select(
            [
                .remove(regionID: "person-1", inset: 0),
                .remove(regionID: "person-2", inset: 0),
            ],
            request: "Swap faces",
            regions: faces
        )
        XCTAssertEqual(kept.count, 2)
        guard case .replaceFaces(let firstSource, let firstDestinations, _) = kept[0],
              case .replaceFaces(let secondSource, let secondDestinations, _) = kept[1]
        else {
            return XCTFail("Expected the two faces to be exchanged")
        }
        XCTAssertEqual(firstSource, "face-1")
        XCTAssertEqual(firstDestinations, ["face-2"])
        XCTAssertEqual(secondSource, "face-2")
        XCTAssertEqual(secondDestinations, ["face-1"])
    }

    func testModelBudgetKeepsTheRequestAndSkipsAPreviewThatWillNotFit() {
        let person = region(
            id: "person-1",
            kind: .person,
            colorName: "blue",
            mask: [UInt8](repeating: 0, count: 16),
            size: 4
        )
        let request = "Remove the man in the blue shirt"
        let fitted = FaceSwapModelBudget.plan(
            request: request,
            regions: [person],
            canAttachImages: true,
            hasPreview: true,
            includeImage: true
        )
        XCTAssertTrue(fitted.attachPreview)
        XCTAssertTrue(fitted.prompt.contains(request))
        XCTAssertTrue(fitted.prompt.contains("attached photo"))

        let tight = FaceSwapModelBudget.plan(
            request: request,
            regions: [person],
            canAttachImages: true,
            hasPreview: true,
            includeImage: true,
            windowTokens: 2_200
        )
        XCTAssertFalse(tight.attachPreview)
        XCTAssertTrue(tight.prompt.contains(request))
        XCTAssertFalse(tight.prompt.contains("attached photo"))

        let retry = FaceSwapModelBudget.plan(
            request: String(repeating: "swap faces ", count: 40),
            regions: [person],
            canAttachImages: true,
            hasPreview: true,
            includeImage: false,
            catalogCap: FaceSwapModelBudget.retryCatalogChars
        )
        XCTAssertFalse(retry.attachPreview)
        XCTAssertTrue(retry.prompt.hasPrefix("swap faces"))
        XCTAssertLessThanOrEqual(
            retry.prompt.split(separator: "\n").first?.count ?? 0,
            FaceSwapModelBudget.maxRequestChars
        )

        let overflow = NSError(
            domain: "FoundationModels.LanguageModelSession.GenerationError",
            code: -1,
            userInfo: [
                NSLocalizedDescriptionKey: "The operation couldn’t be completed. (FoundationModels.LanguageModelSession.GenerationError error -1.)",
            ]
        )
        XCTAssertEqual(
            FaceSwapModelLimits.failure(overflow) as? FaceSwapModelLimitError,
            .contextExceeded
        )
    }

    func testReplaceFacesWritesOnlyDestinationContours() throws {
        let size = 96
        var photo = FaceSwapRaster.solid(width: size, height: size, red: 20, green: 120, blue: 40)
        let pair = facePair()
        paint(&photo, outline: pair.source, red: 220, green: 180, blue: 40)
        paint(&photo, outline: pair.destination, red: 40, green: 50, blue: 90)
        let other = FaceSwapOutline(
            id: "face-3",
            role: .destination,
            refersTo: "another face",
            points: contour(center: CGPoint(x: 0.48, y: 0.78), radiusX: 0.08, radiusY: 0.10)
        )
        paint(&photo, outline: other, red: 180, green: 60, blue: 50)
        let regions = [
            faceRegion(pair.source),
            faceRegion(pair.destination),
            faceRegion(other),
        ]
        let plan = recipe(lightingMatch: 1, colorMatch: 0, detailTransfer: 0)
        let edited = try XCTUnwrap(applyScript(
            [.replaceFaces(sourceID: pair.source.id, destinationIDs: [pair.destination.id, other.id], plan: plan)],
            regions: regions,
            photo: photo
        ))
        XCTAssertEqual(edited.stats.outsideMaskChanged, 0)
        assertUnchangedOutside(original: photo, edited: edited.image, outlines: [pair.destination, other])
        XCTAssertTrue(interiorChanged(original: photo, edited: edited.image, outline: pair.destination))
        XCTAssertTrue(interiorChanged(original: photo, edited: edited.image, outline: other))
        XCTAssertFalse(interiorChanged(original: photo, edited: edited.image, outline: pair.source))
        let outsideBoth = photo.rgb(x: 2, y: 2)
        XCTAssertEqual(outsideBoth?.0, edited.image.rgb(x: 2, y: 2)?.0)
        XCTAssertTrue(edited.log.contains { $0.contains("replaceFaces") })
    }

    func testDiffHighlightsOnlyChangedPixels() {
        let original = FaceSwapRaster.solid(width: 4, height: 2, red: 10, green: 10, blue: 10)
        var edited = original
        edited.setRGB(x: 1, y: 0, red: 200, green: 10, blue: 10)
        let highlight = FaceSwapDiff.highlight(original: original, edited: edited)
        XCTAssertEqual(highlight.rgb(x: 1, y: 0)?.0, 220)
        XCTAssertEqual(highlight.rgb(x: 0, y: 0)?.0, highlight.rgb(x: 0, y: 0)?.1)
        XCTAssertNotEqual(highlight.rgb(x: 0, y: 0)?.0, 220)
    }

    private func applyScript(
        _ commands: [FaceSwapCommand],
        regions: [FaceSwapRegion],
        photo: FaceSwapRaster
    ) -> FaceSwapScriptResult? {
        switch FaceSwapOperations.apply(commands: commands, regions: regions, original: photo) {
        case .success(let result):
            return result
        case .failure(let error):
            XCTFail(error.message)
            return nil
        }
    }

    private func region(
        id: String,
        kind: FaceSwapRegion.Kind,
        colorName: String,
        mask: [UInt8],
        size: Int
    ) -> FaceSwapRegion {
        FaceSwapRegion(
            id: id,
            kind: kind,
            place: "left, middle",
            colorName: colorName,
            points: [
                CGPoint(x: 0.08, y: 0.16),
                CGPoint(x: 0.16, y: 0.16),
                CGPoint(x: 0.29, y: 0.16),
                CGPoint(x: 0.29, y: 0.30),
                CGPoint(x: 0.29, y: 0.42),
                CGPoint(x: 0.16, y: 0.42),
                CGPoint(x: 0.08, y: 0.42),
                CGPoint(x: 0.08, y: 0.30),
            ],
            mask: mask,
            onID: nil
        )
    }

    private func faceRegion(_ outline: FaceSwapOutline) -> FaceSwapRegion {
        FaceSwapRegion(
            id: outline.id,
            kind: .face,
            place: "center, middle",
            colorName: "tan",
            points: outline.points,
            mask: nil,
            onID: nil
        )
    }

    private func maskRect(x: Int, y: Int, width: Int, height: Int, imageWidth: Int, imageHeight: Int) -> [UInt8] {
        var mask = [UInt8](repeating: 0, count: imageWidth * imageHeight)
        for row in y..<(y + height) {
            for column in x..<(x + width) {
                mask[row * imageWidth + column] = 255
            }
        }
        return mask
    }

    private func paint(_ raster: inout FaceSwapRaster, mask: [UInt8], red: UInt8, green: UInt8, blue: UInt8) {
        for y in 0..<raster.height {
            for x in 0..<raster.width where mask[y * raster.width + x] > 0 {
                raster.setRGB(x: x, y: y, red: red, green: green, blue: blue)
            }
        }
    }

    private func assertUnchanged(original: FaceSwapRaster, edited: FaceSwapRaster, outside mask: [UInt8]) {
        for y in 0..<original.height {
            for x in 0..<original.width {
                if mask[y * original.width + x] > 0 { continue }
                XCTAssertEqual(original.rgb(x: x, y: y)?.0, edited.rgb(x: x, y: y)?.0)
                XCTAssertEqual(original.rgb(x: x, y: y)?.1, edited.rgb(x: x, y: y)?.1)
                XCTAssertEqual(original.rgb(x: x, y: y)?.2, edited.rgb(x: x, y: y)?.2)
            }
        }
    }

    private func recipe(lightingMatch: Double, colorMatch: Double, detailTransfer: Double) -> FaceSwapEditPlan {
        FaceSwapEditPlan(
            fitPose: 0,
            lightingMatch: lightingMatch,
            colorMatch: colorMatch,
            detailTransfer: detailTransfer,
            edgeBand: 0.02,
            inset: 0,
            motive: "Keep the destination light.",
            tightenedDestination: []
        )
    }

    private func apply(
        plan: FaceSwapEditPlan,
        pair: (source: FaceSwapOutline, destination: FaceSwapOutline),
        photo: FaceSwapRaster,
        sourceLandmarks: FaceSwapLandmarkTrio? = nil,
        destinationLandmarks: FaceSwapLandmarkTrio? = nil
    ) -> FaceSwapPasteOutput? {
        switch FaceSwapEditor.apply(
            plan: plan,
            source: pair.source,
            destination: pair.destination,
            original: photo,
            working: photo,
            sourceLandmarks: sourceLandmarks,
            destinationLandmarks: destinationLandmarks
        ) {
        case .success(let output):
            return output
        case .failure(let error):
            XCTFail(error.message)
            return nil
        }
    }

    private func facePair() -> (source: FaceSwapOutline, destination: FaceSwapOutline) {
        (
            source: FaceSwapOutline(
                id: "source-face",
                role: .source,
                refersTo: "the man's face",
                points: contour(center: CGPoint(x: 0.28, y: 0.42), radiusX: 0.12, radiusY: 0.16)
            ),
            destination: FaceSwapOutline(
                id: "destination-face",
                role: .destination,
                refersTo: "the woman's face",
                points: contour(center: CGPoint(x: 0.70, y: 0.50), radiusX: 0.11, radiusY: 0.15)
            )
        )
    }

    private func contour(center: CGPoint, radiusX: CGFloat, radiusY: CGFloat) -> [CGPoint] {
        (0..<12).map { index in
            let angle = CGFloat(index) / 12 * 2 * .pi - .pi / 2
            return CGPoint(
                x: center.x + cos(angle) * radiusX,
                y: center.y + sin(angle) * radiusY
            )
        }
    }

    private func paintEye(_ raster: inout FaceSwapRaster, at point: CGPoint, red: UInt8, green: UInt8, blue: UInt8) {
        let originX = Int(point.x.rounded())
        let originY = Int(point.y.rounded())
        for y in (originY - 1)...(originY + 1) {
            for x in (originX - 1)...(originX + 1) {
                raster.setRGB(x: x, y: y, red: red, green: green, blue: blue)
            }
        }
    }

    private func paint(_ raster: inout FaceSwapRaster, outline: FaceSwapOutline, red: UInt8, green: UInt8, blue: UInt8) {
        let polygon = FaceSwapOutlineValidation.pixelPoints(outline, width: raster.width, height: raster.height, inset: 0)
        for y in 0..<raster.height {
            for x in 0..<raster.width {
                let sample = CGPoint(x: Double(x) + 0.5, y: Double(y) + 0.5)
                if FaceSwapOutlineValidation.contains(sample, polygon: polygon) {
                    raster.setRGB(x: x, y: y, red: red, green: green, blue: blue)
                }
            }
        }
    }

    private func assertUnchangedOutside(original: FaceSwapRaster, edited: FaceSwapRaster, outline: FaceSwapOutline) {
        assertUnchangedOutside(original: original, edited: edited, outlines: [outline])
    }

    private func assertUnchangedOutside(original: FaceSwapRaster, edited: FaceSwapRaster, outlines: [FaceSwapOutline]) {
        let polygons = outlines.map {
            FaceSwapOutlineValidation.pixelPoints($0, width: original.width, height: original.height, inset: 0)
        }
        for y in 0..<original.height {
            for x in 0..<original.width {
                let sample = CGPoint(x: Double(x) + 0.5, y: Double(y) + 0.5)
                if polygons.contains(where: { FaceSwapOutlineValidation.contains(sample, polygon: $0) }) { continue }
                XCTAssertEqual(original.rgb(x: x, y: y)?.0, edited.rgb(x: x, y: y)?.0)
                XCTAssertEqual(original.rgb(x: x, y: y)?.1, edited.rgb(x: x, y: y)?.1)
                XCTAssertEqual(original.rgb(x: x, y: y)?.2, edited.rgb(x: x, y: y)?.2)
            }
        }
    }

    private func interiorChanged(original: FaceSwapRaster, edited: FaceSwapRaster, outline: FaceSwapOutline) -> Bool {
        let polygon = FaceSwapOutlineValidation.pixelPoints(outline, width: original.width, height: original.height, inset: 0)
        for y in 0..<original.height {
            for x in 0..<original.width {
                let sample = CGPoint(x: Double(x) + 0.5, y: Double(y) + 0.5)
                guard FaceSwapOutlineValidation.contains(sample, polygon: polygon) else { continue }
                let before = original.rgb(x: x, y: y)
                let after = edited.rgb(x: x, y: y)
                if before?.0 != after?.0 || before?.1 != after?.1 || before?.2 != after?.2 {
                    return true
                }
            }
        }
        return false
    }

    private func interiorLuma(of raster: FaceSwapRaster, outline: FaceSwapOutline) -> (luma: Double, count: Int) {
        let polygon = FaceSwapOutlineValidation.pixelPoints(outline, width: raster.width, height: raster.height, inset: 0)
        let bounds = FaceSwapOutlineValidation.boundsOf(polygon)
        let insetX = bounds.width * 0.28
        let insetY = bounds.height * 0.28
        let core = bounds.insetBy(dx: insetX, dy: insetY)
        var sum = 0.0
        var count = 0
        let minX = max(0, Int(core.minX.rounded(.up)))
        let maxX = min(raster.width - 1, Int(core.maxX.rounded(.down)))
        let minY = max(0, Int(core.minY.rounded(.up)))
        let maxY = min(raster.height - 1, Int(core.maxY.rounded(.down)))
        guard minX <= maxX, minY <= maxY else { return (0, 0) }
        for y in minY...maxY {
            for x in minX...maxX {
                let sample = CGPoint(x: Double(x) + 0.5, y: Double(y) + 0.5)
                guard FaceSwapOutlineValidation.contains(sample, polygon: polygon),
                      let color = raster.rgb(x: x, y: y)
                else { continue }
                sum += 0.2126 * Double(color.0) + 0.7152 * Double(color.1) + 0.0722 * Double(color.2)
                count += 1
            }
        }
        guard count > 0 else { return (0, 0) }
        return (sum / Double(count), count)
    }
}

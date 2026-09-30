import CoreImage
import Vision

/// Runs person segmentation and face landmarks, then keeps pixels that match the hair.
enum HairFrameProcessor {
    static func makeRequests() -> (person: VNGeneratePersonSegmentationRequest, face: VNDetectFaceLandmarksRequest) {
        let person = VNGeneratePersonSegmentationRequest()
        person.qualityLevel = .balanced
        person.outputPixelFormat = kCVPixelFormatType_OneComponent8
        return (person, VNDetectFaceLandmarksRequest())
    }

    /// Mask for an upright image. Nil when no face is in frame, so the preview stays undyed.
    static func hairMask(
        for image: CIImage,
        personRequest: VNGeneratePersonSegmentationRequest,
        faceRequest: VNDetectFaceLandmarksRequest
    ) -> CIImage? {
        let handler = VNImageRequestHandler(ciImage: image, orientation: .up, options: [:])
        do {
            try handler.perform([personRequest, faceRequest])
        } catch {
            return nil
        }
        guard let faces = faceRequest.results, !faces.isEmpty else { return nil }
        guard let personBuffer = personRequest.results?.first?.pixelBuffer else { return nil }
        return hairMask(personBuffer: personBuffer, faces: faces, image: image)
    }

    static func hairMask(personBuffer: CVPixelBuffer, faces: [VNFaceObservation], image: CIImage) -> CIImage? {
        let regions = HairRegionBuilder.regions(for: HairFaceGuideBuilder.guides(from: faces))
        guard !regions.isEmpty else { return nil }

        let width = CVPixelBufferGetWidth(personBuffer)
        let height = CVPixelBufferGetHeight(personBuffer)
        guard width > 0, height > 0 else { return nil }
        guard let colors = HairImageSampler.colors(from: image, width: width, height: height) else { return nil }

        CVPixelBufferLockBaseAddress(personBuffer, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(personBuffer, .readOnly) }
        guard let base = CVPixelBufferGetBaseAddress(personBuffer) else { return nil }
        let rowBytes = CVPixelBufferGetBytesPerRow(personBuffer)
        var person = [UInt8](repeating: 0, count: width * height)
        for y in 0..<height {
            let row = base.advanced(by: y * rowBytes)
            for x in 0..<width {
                person[(y * width) + x] = row.load(fromByteOffset: x, as: UInt8.self)
            }
        }
        let bytes = HairAffinity.maskBytes(
            colors: colors,
            person: person,
            width: width,
            height: height,
            regions: regions
        )
        return HairMaskImage.make(bytes: bytes, width: width, height: height)
    }
}

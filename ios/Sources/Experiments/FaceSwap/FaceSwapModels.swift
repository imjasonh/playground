import CoreGraphics
import Foundation

/// What the photo view is showing after an edit.
enum FaceSwapViewMode: String, CaseIterable, Identifiable {
    case result
    case diff

    var id: String { rawValue }

    var title: String {
        switch self {
        case .result: return "Result"
        case .diff: return "Diff"
        }
    }
}

/// Failure text for `Result` values. `String` does not conform to `Error`.
struct FaceSwapMessageError: Error, Equatable, LocalizedError, ExpressibleByStringInterpolation, Sendable {
    var message: String

    var errorDescription: String? { message }

    init(_ message: String) {
        self.message = message
    }

    init(stringLiteral value: String) {
        self.message = value
    }

    init(stringInterpolation: DefaultStringInterpolation) {
        self.message = String(stringInterpolation: stringInterpolation)
    }
}

struct FaceSwapEditStats: Equatable, Sendable {
    var sourceID: String
    var destinationID: String
    var writtenPixels: Int
    var changedFromOriginal: Int
    var totalPixels: Int
    var outsideMaskChanged: Int
    var warp: String

    var percentChanged: Double {
        guard totalPixels > 0 else { return 0 }
        return Double(changedFromOriginal) / Double(totalPixels) * 100
    }
}

enum FaceSwapDiff {
    static func changedPixelCount(original: FaceSwapRaster, edited: FaceSwapRaster) -> Int {
        guard original.width == edited.width, original.height == edited.height else { return 0 }
        var count = 0
        let pixels = original.pixelCount
        for pixel in 0..<pixels {
            let offset = pixel * 4
            if original.rgba[offset] != edited.rgba[offset]
                || original.rgba[offset + 1] != edited.rgba[offset + 1]
                || original.rgba[offset + 2] != edited.rgba[offset + 2]
            {
                count += 1
            }
        }
        return count
    }

    static func summary(original: FaceSwapRaster, edited: FaceSwapRaster) -> String {
        let changed = changedPixelCount(original: original, edited: edited)
        let total = original.pixelCount
        let percent = total == 0 ? 0 : Double(changed) / Double(total) * 100
        return "Changed \(changed) of \(total) pixels (\(String(format: "%.1f", percent))%)."
    }

    /// Gray original, red where any channel differs. The red region is the edit.
    static func highlight(original: FaceSwapRaster, edited: FaceSwapRaster) -> FaceSwapRaster {
        guard original.width == edited.width, original.height == edited.height else { return original }
        var output = original.copy()
        let pixels = original.pixelCount
        for pixel in 0..<pixels {
            let offset = pixel * 4
            let changed = original.rgba[offset] != edited.rgba[offset]
                || original.rgba[offset + 1] != edited.rgba[offset + 1]
                || original.rgba[offset + 2] != edited.rgba[offset + 2]
            if changed {
                output.rgba[offset] = 220
                output.rgba[offset + 1] = 32
                output.rgba[offset + 2] = 42
            } else {
                let luma = (Int(original.rgba[offset]) * 54
                    + Int(original.rgba[offset + 1]) * 183
                    + Int(original.rgba[offset + 2]) * 19) / 256
                let dim = UInt8(luma / 3)
                output.rgba[offset] = dim
                output.rgba[offset + 1] = dim
                output.rgba[offset + 2] = dim
            }
            output.rgba[offset + 3] = 255
        }
        return output
    }
}

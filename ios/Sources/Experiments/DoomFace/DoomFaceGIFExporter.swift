import UIKit

/// GIF of captured faces in Doom's idle look order (left, center, right, center).
enum DoomFaceGIFExporter {
    static let frameDelay: Double = 0.22
    static let maxDimension: CGFloat = 240

    static func idleLookSequence(health: Int) -> [DoomFaceSlot] {
        [.lookLeft, .lookCenter, .lookRight, .lookCenter].map {
            DoomFaceSlot(health: health, expression: $0)
        }
    }

    static func frames(from captures: [DoomFaceSlot: UIImage]) -> [UIImage] {
        guard !captures.isEmpty else { return [] }

        var bestHealth = 0
        var bestCount = -1
        for health in 0..<DoomFaceSheetLayout.healthRowCount {
            let count = [DoomFaceExpression.lookLeft, .lookCenter, .lookRight]
                .filter { captures[DoomFaceSlot(health: health, expression: $0)] != nil }
                .count
            if count > bestCount {
                bestCount = count
                bestHealth = health
            }
        }

        if bestCount >= 2 {
            let sequence = idleLookSequence(health: bestHealth).compactMap { captures[$0] }
            if sequence.count >= 2 { return sequence }
        }

        return DoomFaceSheetLayout.allSlots.compactMap { captures[$0] }
    }

    static func makeGIF(captures: [DoomFaceSlot: UIImage]) -> Data? {
        let images = frames(from: captures)
        guard images.count >= 2 else { return nil }
        return WiggleGIFEncoder.makeGIFData(
            frames: images,
            frameDelay: frameDelay,
            maxDimension: maxDimension
        )
    }

    static func writeTemporaryGIF(captures: [DoomFaceSlot: UIImage]) throws -> URL {
        guard let data = makeGIF(captures: captures) else {
            throw ExportError.notEnoughFaces
        }
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("doomface-\(UUID().uuidString)")
            .appendingPathExtension("gif")
        try data.write(to: url, options: .atomic)
        return url
    }

    enum ExportError: LocalizedError {
        case notEnoughFaces

        var errorDescription: String? {
            "Capture at least two faces before exporting a GIF."
        }
    }
}

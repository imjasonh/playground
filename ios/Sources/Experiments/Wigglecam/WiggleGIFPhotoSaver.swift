import Photos
import UIKit

/// Saves Wigglecam output into the user's photo library (add-only access).
enum WiggleGIFPhotoSaver {
    enum SaveError: LocalizedError {
        case notAuthorized
        case encodingFailed
        case saveFailed(String)

        var errorDescription: String? {
            switch self {
            case .notAuthorized:
                return "Photos access is required to save. Enable it in Settings."
            case .encodingFailed:
                return "Could not encode the image data."
            case .saveFailed(let message):
                return message
            }
        }
    }

    static func saveGIF(_ data: Data) async throws {
        try await savePhotoResources([data])
    }

    /// Writes the stereo pair as two JPEG stills (left, then right).
    static func saveStereoJPEGs(
        left: UIImage,
        right: UIImage,
        quality: CGFloat = 0.92
    ) async throws {
        guard
            let leftData = left.jpegData(compressionQuality: quality),
            let rightData = right.jpegData(compressionQuality: quality)
        else {
            throw SaveError.encodingFailed
        }
        try await savePhotoResources([leftData, rightData])
    }

    private static func savePhotoResources(_ payloads: [Data]) async throws {
        guard !payloads.isEmpty else { return }
        let status = await requestAddOnlyAccess()
        guard status == .authorized || status == .limited else {
            throw SaveError.notAuthorized
        }

        try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<Void, Error>) in
            PHPhotoLibrary.shared().performChanges({
                for data in payloads {
                    let request = PHAssetCreationRequest.forAsset()
                    request.addResource(with: .photo, data: data, options: nil)
                }
            }, completionHandler: { success, error in
                if let error {
                    continuation.resume(throwing: SaveError.saveFailed(error.localizedDescription))
                } else if success {
                    continuation.resume()
                } else {
                    continuation.resume(throwing: SaveError.saveFailed("Could not save to Photos."))
                }
            })
        }
    }

    @MainActor
    private static func requestAddOnlyAccess() async -> PHAuthorizationStatus {
        let current = PHPhotoLibrary.authorizationStatus(for: .addOnly)
        switch current {
        case .notDetermined:
            return await PHPhotoLibrary.requestAuthorization(for: .addOnly)
        default:
            return current
        }
    }
}

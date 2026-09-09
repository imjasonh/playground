import Photos
import UIKit

/// Saves a Face Swap photo into the user's library (add-only access).
enum FaceSwapPhotoSaver {
    enum SaveError: LocalizedError {
        case notAuthorized
        case encodingFailed
        case saveFailed(String)

        var errorDescription: String? {
            switch self {
            case .notAuthorized:
                return "Photos access is required to save. Enable it in Settings."
            case .encodingFailed:
                return "Could not encode the photo."
            case .saveFailed(let message):
                return message
            }
        }
    }

    static func saveJPEG(_ image: UIImage, quality: CGFloat = 0.92) async throws {
        guard let data = image.jpegData(compressionQuality: quality) else {
            throw SaveError.encodingFailed
        }
        let status = await requestAddOnlyAccess()
        guard status == .authorized || status == .limited else {
            throw SaveError.notAuthorized
        }
        try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<Void, Error>) in
            PHPhotoLibrary.shared().performChanges({
                let request = PHAssetCreationRequest.forAsset()
                request.addResource(with: .photo, data: data, options: nil)
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

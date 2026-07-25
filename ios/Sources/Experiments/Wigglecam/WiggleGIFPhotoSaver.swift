import Photos
import UIKit

/// Saves an animated GIF into the user's photo library (add-only access).
enum WiggleGIFPhotoSaver {
    enum SaveError: LocalizedError {
        case notAuthorized
        case saveFailed(String)

        var errorDescription: String? {
            switch self {
            case .notAuthorized:
                return "Photos access is required to save the GIF. Enable it in Settings."
            case .saveFailed(let message):
                return message
            }
        }
    }

    static func saveGIF(_ data: Data) async throws {
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
                    continuation.resume(throwing: SaveError.saveFailed("Could not save the GIF to Photos."))
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

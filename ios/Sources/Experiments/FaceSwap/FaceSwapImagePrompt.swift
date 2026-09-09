import Foundation

enum FaceSwapImageError: LocalizedError, Equatable {
    case imageInputUnavailable
    case missingEditPlan

    var errorDescription: String? {
        switch self {
        case .imageInputUnavailable:
            return "Face Swap needs the on-device model on iOS 26 or later."
        case .missingEditPlan:
            return "The model did not choose an edit. No pixels changed."
        }
    }
}

/// The SDK this app builds with has no `FoundationModels.Attachment`, so the
/// session never attaches a photo. Matching uses the region catalog instead.
enum FaceSwapImagePromptSupport {
    static var canAttachImages: Bool { false }
}

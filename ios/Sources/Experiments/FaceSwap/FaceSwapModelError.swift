import Foundation

enum FaceSwapModelError: LocalizedError, Equatable {
    case missingEditPlan

    var errorDescription: String? {
        switch self {
        case .missingEditPlan:
            return "The model did not choose an edit. No pixels changed."
        }
    }
}

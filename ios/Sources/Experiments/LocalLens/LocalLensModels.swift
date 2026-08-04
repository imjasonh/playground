import CoreGraphics
import Foundation

/// Which on-device Vision request Local Lens runs on each camera frame.
enum LocalLensMode: String, CaseIterable, Identifiable, Equatable {
    case classify
    case text
    case animals
    case faces
    case people
    case barcodes

    var id: String { rawValue }

    var title: String {
        switch self {
        case .classify: return "Classify"
        case .text: return "Text"
        case .animals: return "Animals"
        case .faces: return "Faces"
        case .people: return "People"
        case .barcodes: return "Codes"
        }
    }

    var symbolName: String {
        switch self {
        case .classify: return "sparkles"
        case .text: return "text.viewfinder"
        case .animals: return "pawprint"
        case .faces: return "face.smiling"
        case .people: return "figure.stand"
        case .barcodes: return "barcode.viewfinder"
        }
    }

    var blurb: String {
        switch self {
        case .classify:
            return "Scene and object labels from Apple’s on-device classifier."
        case .text:
            return "Live OCR — read text in the frame without leaving the device."
        case .animals:
            return "Recognize cats and dogs with Vision’s animal request."
        case .faces:
            return "Find faces and draw their boxes."
        case .people:
            return "Detect human body rectangles in the frame."
        case .barcodes:
            return "Scan QR codes and barcodes on-device."
        }
    }
}

/// One label / detection produced by a Vision pass.
struct LocalLensFinding: Equatable, Identifiable {
    let id: String
    let label: String
    let confidence: Double
    /// Vision-normalized bounding box (origin bottom-left, 0…1). Nil for whole-image labels.
    let boundingBox: CGRect?

    init(id: String = UUID().uuidString, label: String, confidence: Double, boundingBox: CGRect? = nil) {
        self.id = id
        self.label = label
        self.confidence = confidence
        self.boundingBox = boundingBox
    }
}

/// Ranked findings for one analyzed frame.
struct LocalLensFrameResult: Equatable {
    let mode: LocalLensMode
    let findings: [LocalLensFinding]
    let analyzedAt: Date

    static func empty(mode: LocalLensMode, at date: Date = Date()) -> LocalLensFrameResult {
        LocalLensFrameResult(mode: mode, findings: [], analyzedAt: date)
    }
}

/// Pure helpers for filtering, ranking, and formatting Vision output.
enum LocalLensResultBuilder {
    /// Minimum confidence kept for classify / animal labels (0…1).
    static let defaultMinimumConfidence = 0.15
    /// How many labels to show in the overlay.
    static let defaultMaxFindings = 6

    static func build(
        mode: LocalLensMode,
        findings: [LocalLensFinding],
        minimumConfidence: Double = defaultMinimumConfidence,
        maxFindings: Int = defaultMaxFindings,
        at date: Date = Date()
    ) -> LocalLensFrameResult {
        let ranked = findings
            .filter { $0.confidence >= minimumConfidence && !$0.label.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty }
            .sorted { lhs, rhs in
                if lhs.confidence != rhs.confidence {
                    return lhs.confidence > rhs.confidence
                }
                return lhs.label.localizedCaseInsensitiveCompare(rhs.label) == .orderedAscending
            }
        return LocalLensFrameResult(
            mode: mode,
            findings: Array(ranked.prefix(max(0, maxFindings))),
            analyzedAt: date
        )
    }

    static func confidencePercent(_ confidence: Double) -> Int {
        Int((confidence * 100).rounded())
    }

    static func confidenceLabel(_ confidence: Double) -> String {
        "\(confidencePercent(confidence))%"
    }

    /// Human-readable chip text for a finding.
    static func chipText(for finding: LocalLensFinding) -> String {
        "\(finding.label) · \(confidenceLabel(finding.confidence))"
    }

    /// Status line when the latest pass returned nothing useful.
    static func emptyStatus(for mode: LocalLensMode) -> String {
        switch mode {
        case .classify:
            return "Point at a scene — labels appear when the on-device model is confident."
        case .text:
            return "Point at printed or on-screen text."
        case .animals:
            return "Looking for cats and dogs…"
        case .faces:
            return "No faces in frame."
        case .people:
            return "No people detected."
        case .barcodes:
            return "Point at a QR code or barcode."
        }
    }
}

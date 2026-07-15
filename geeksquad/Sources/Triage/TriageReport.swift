import Foundation
#if canImport(FoundationModels)
import FoundationModels
#endif

/// Structured closing card for a triage turn (design: likelyCause + evidence + steps).
#if canImport(FoundationModels)
@available(macOS 26.0, *)
@Generable
struct TriageReport: Equatable {
    @Guide(description: "One-line summary of the situation")
    var headline: String

    @Guide(description: "Most likely cause based only on tool evidence")
    var likelyCause: String

    @Guide(description: "Short evidence bullets citing tool findings")
    var evidence: [String]

    @Guide(description: "Numbered actions the user can take; do not claim you applied them")
    var proposedSteps: [String]
}
#endif

/// UI-safe copy of a triage report (works when FoundationModels isn't linked).
struct TriageReportViewModel: Equatable {
    var headline: String
    var likelyCause: String
    var evidence: [String]
    var proposedSteps: [String]

    var markdown: String {
        var lines = [
            "## \(headline)",
            "",
            "**Likely cause:** \(likelyCause)",
            "",
            "**Evidence:**",
        ]
        for item in evidence {
            lines.append("- \(item)")
        }
        lines.append("")
        lines.append("**Proposed steps (not applied):**")
        for (i, step) in proposedSteps.enumerated() {
            lines.append("\(i + 1). \(step)")
        }
        return lines.joined(separator: "\n")
    }

    #if canImport(FoundationModels)
    @available(macOS 26.0, *)
    init(_ report: TriageReport) {
        headline = report.headline
        likelyCause = report.likelyCause
        evidence = report.evidence
        proposedSteps = report.proposedSteps
    }
    #endif

    init(headline: String, likelyCause: String, evidence: [String], proposedSteps: [String]) {
        self.headline = headline
        self.likelyCause = likelyCause
        self.evidence = evidence
        self.proposedSteps = proposedSteps
    }
}

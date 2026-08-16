import Foundation

/// Filters blank / placeholder remediations so UI and markdown omit “next steps”
/// when there is nothing for the user to do.
enum RemediationCopy {
    static func actionable(_ steps: [String]) -> [String] {
        steps
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty && !isNoOp($0) }
    }

    /// Placeholders the model (or toolbox) sometimes emits instead of leaving the list empty.
    static func isNoOp(_ step: String) -> Bool {
        let t = step.lowercased()
        if t == "none" || t == "n/a" || t == "na" || t == "-" || t == "nil" {
            return true
        }
        let markers = [
            "no specific action",
            "no action required",
            "no actions required",
            "no further action",
            "nothing to do",
            "no changes needed",
            "no change needed",
            "no steps needed",
            "no steps required",
            "no remediation",
            "no proposed step",
            "nothing required",
        ]
        return markers.contains { t.contains($0) }
    }
}

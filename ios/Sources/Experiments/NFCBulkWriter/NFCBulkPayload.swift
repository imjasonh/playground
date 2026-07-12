import Foundation

/// What kind of NDEF record the bulk writer should encode.
enum NFCBulkPayloadKind: String, CaseIterable, Identifiable {
    case text
    case url

    var id: String { rawValue }

    var title: String {
        switch self {
        case .text: return "Text"
        case .url: return "URL"
        }
    }

    var fieldLabel: String {
        switch self {
        case .text: return "Text to write"
        case .url: return "URL to write"
        }
    }

    var placeholder: String {
        switch self {
        case .text: return "Hello from Playground"
        case .url: return "https://example.com"
        }
    }
}

/// User-edited draft of the payload that will be written to every tapped tag.
struct NFCBulkPayloadDraft: Equatable {
    var kind: NFCBulkPayloadKind = .url
    var text: String = ""

    /// Trimmed content used for validation and encoding.
    var trimmedText: String {
        text.trimmingCharacters(in: .whitespacesAndNewlines)
    }

    var isEmpty: Bool { trimmedText.isEmpty }

    /// Normalized URL string when `kind == .url`, otherwise `nil`.
    var normalizedURLString: String? {
        guard kind == .url else { return nil }
        return Self.normalizeURLString(trimmedText)
    }

    var isValid: Bool {
        validationError == nil
    }

    /// Human-readable reason the draft cannot be written, or `nil` when ready.
    var validationError: String? {
        if trimmedText.isEmpty {
            return "Enter a payload before starting."
        }
        switch kind {
        case .text:
            return nil
        case .url:
            guard normalizedURLString != nil else {
                return "Enter a valid URL (http:// or https://)."
            }
            return nil
        }
    }

    /// Accept bare hosts by prepending `https://`, and require an http(s) URL.
    static func normalizeURLString(_ raw: String) -> String? {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }

        let candidate: String
        if let scheme = URL(string: trimmed)?.scheme?.lowercased(),
           scheme == "http" || scheme == "https" {
            candidate = trimmed
        } else if trimmed.contains("://") {
            return nil
        } else {
            candidate = "https://\(trimmed)"
        }

        guard let url = URL(string: candidate),
              let scheme = url.scheme?.lowercased(),
              scheme == "http" || scheme == "https",
              url.host != nil
        else {
            return nil
        }
        return candidate
    }
}

import Foundation
import CoreNFC

/// Builds `NFCNDEFMessage` values from a validated payload draft.
enum NFCBulkNDEFBuilder {
    enum BuildError: LocalizedError, Equatable {
        case emptyPayload
        case invalidURL
        case encodingFailed

        var errorDescription: String? {
            switch self {
            case .emptyPayload:
                return "Enter a payload before starting."
            case .invalidURL:
                return "Enter a valid URL (http:// or https://)."
            case .encodingFailed:
                return "Could not encode that payload as NDEF."
            }
        }
    }

    static func message(from draft: NFCBulkPayloadDraft) throws -> NFCNDEFMessage {
        guard draft.isValid else {
            if draft.isEmpty { throw BuildError.emptyPayload }
            if draft.kind == .url { throw BuildError.invalidURL }
            throw BuildError.emptyPayload
        }

        switch draft.kind {
        case .text:
            guard let payload = NFCNDEFPayload.wellKnownTypeTextPayload(
                string: draft.trimmedText,
                locale: Locale(identifier: "en")
            ) else {
                throw BuildError.encodingFailed
            }
            return NFCNDEFMessage(records: [payload])

        case .url:
            guard let urlString = draft.normalizedURLString,
                  let url = URL(string: urlString),
                  let payload = NFCNDEFPayload.wellKnownTypeURIPayload(url: url)
            else {
                throw BuildError.invalidURL
            }
            return NFCNDEFMessage(records: [payload])
        }
    }

    /// Approximate byte length of the encoded NDEF payload (for capacity checks).
    static func estimatedByteCount(of draft: NFCBulkPayloadDraft) -> Int {
        switch draft.kind {
        case .text:
            // Status byte + language code ("en") + UTF-8 text.
            return 1 + 2 + draft.trimmedText.utf8.count
        case .url:
            let urlString = draft.normalizedURLString ?? draft.trimmedText
            // URI identifier code byte + abbreviated remainder (best-effort).
            let withoutScheme = urlString
                .replacingOccurrences(of: "https://", with: "", options: [.anchored, .caseInsensitive])
                .replacingOccurrences(of: "http://", with: "", options: [.anchored, .caseInsensitive])
            return 1 + withoutScheme.utf8.count
        }
    }
}

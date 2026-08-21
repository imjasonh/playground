import Foundation

/// Pure helpers for NFC Tags scan results (no Core NFC types).
enum NFCTagScanFormatter {
    /// Core NFC `NFCReaderError.ndefReaderSessionErrorZeroLengthMessage` raw value.
    static let zeroLengthNDEFMessageErrorCode = 403

    /// Formats a tag UID as colon-separated hex (`04:D3:E8:…`).
    static func uidHex(_ data: Data) -> String {
        data.map { String(format: "%02X", $0) }.joined(separator: ":")
    }

    /// True when Core NFC reports an NDEF-capable tag with no message (blank tag).
    static func isEmptyNDEFErrorCode(_ code: Int) -> Bool {
        code == zeroLengthNDEFMessageErrorCode
    }

    /// Multiline "Last read" body for a blank or empty NDEF tag.
    static func blankTagSummary(
        writable: Bool,
        capacity: Int,
        uid: String?,
        family: String?
    ) -> String {
        var lines = [
            "Blank NDEF tag (\(writable ? "writable" : "read-only"))",
        ]
        if capacity > 0 {
            lines.append("NDEF capacity: \(capacity) bytes")
        }
        appendIdentity(uid: uid, family: family, to: &lines)
        return lines.joined(separator: "\n")
    }

    /// Multiline "Last read" body when the tag is not NDEF-formatted.
    static func nonNDEFSummary(uid: String?, family: String?) -> String {
        var lines = ["Tag detected, but it has no NDEF message."]
        appendIdentity(uid: uid, family: family, to: &lines)
        lines.append("Use Write to store text or a URL on a blank phone-writable tag.")
        return lines.joined(separator: "\n")
    }

    /// Multiline "Last read" body after decoding NDEF records, with optional hardware lines.
    static func recordsSummary(
        _ recordsBody: String,
        uid: String?,
        family: String?
    ) -> String {
        var lines = [recordsBody]
        appendIdentity(uid: uid, family: family, to: &lines)
        return lines.joined(separator: "\n")
    }

    private static func appendIdentity(uid: String?, family: String?, to lines: inout [String]) {
        if let family, !family.isEmpty {
            lines.append("Type: \(family)")
        }
        if let uid, !uid.isEmpty {
            lines.append("UID: \(uid)")
        }
    }
}

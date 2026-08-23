import Foundation

/// What the Write tab stores on an NDEF tag.
enum NFCNDEFContentKind: String, CaseIterable, Identifiable {
    case text
    case url

    var id: String { rawValue }

    var title: String {
        switch self {
        case .text: return "Text"
        case .url: return "URL"
        }
    }
}

/// User-edited payload for a write session.
struct NFCNDEFWriteDraft: Equatable {
    var kind: NFCNDEFContentKind = .text
    var text: String = ""
}

/// One decoded NDEF record for the Read UI.
struct NFCNDEFDecodedRecord: Equatable {
    var typeLabel: String
    var body: String
}

/// Raw NDEF record fields used to compare write intent vs read-back.
struct NFCNDEFRecordSnapshot: Equatable {
    var typeNameFormatRawValue: UInt8
    var type: Data
    var payload: Data
}

/// Pure NDEF text / URI codec and draft validation (no Core NFC).
enum NFCNDEFCodec {
    /// Returns true when both messages have the same record count and each
    /// record's type name format, type bytes, and payload bytes match.
    static func ndefRecordsMatch(
        _ lhs: [NFCNDEFRecordSnapshot],
        _ rhs: [NFCNDEFRecordSnapshot]
    ) -> Bool {
        lhs == rhs
    }

    /// Returns a user-facing error when the draft cannot be written; otherwise `nil`.
    static func validationError(for draft: NFCNDEFWriteDraft) -> String? {
        let trimmed = draft.text.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed.isEmpty {
            return "Enter text or a URL to write."
        }
        if draft.kind == .url {
            guard let url = URL(string: trimmed),
                  let scheme = url.scheme,
                  !scheme.isEmpty,
                  url.host != nil || scheme == "mailto" || scheme == "tel" || scheme == "sms"
            else {
                return "That does not look like a valid URL."
            }
        }
        return nil
    }

    /// Encodes a well-known Text record payload (status + language + UTF-8 body).
    static func encodeTextPayload(text: String, languageCode: String = "en") -> Data {
        let language = Data(languageCode.utf8)
        let status = UInt8(language.count & 0x3F) // UTF-8
        var data = Data([status])
        data.append(language)
        data.append(Data(text.utf8))
        return data
    }

    /// Decodes a well-known Text record payload into language code and body.
    static func decodeTextPayload(_ payload: Data) -> (languageCode: String, text: String)? {
        guard let status = payload.first else { return nil }
        let languageLength = Int(status & 0x3F)
        let isUTF16 = (status & 0x80) != 0
        guard payload.count >= 1 + languageLength else { return nil }
        let languageData = payload.subdata(in: 1..<(1 + languageLength))
        let bodyData = payload.subdata(in: (1 + languageLength)..<payload.count)
        let languageCode = String(data: languageData, encoding: .utf8) ?? ""
        // NFC Forum Text RTD uses UTF-16 BE when the UTF-16 flag is set.
        let encoding: String.Encoding = isUTF16 ? .utf16BigEndian : .utf8
        guard let text = String(data: bodyData, encoding: encoding) else { return nil }
        return (languageCode, text)
    }

    /// Encodes a well-known URI record payload (identifier code + UTF-8 remainder).
    static func encodeURIPayload(urlString: String) -> Data? {
        let trimmed = urlString.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }
        let (code, remainder) = uriPrefix(for: trimmed)
        var data = Data([code])
        data.append(Data(remainder.utf8))
        return data
    }

    /// Decodes a well-known URI record payload into a full URL string.
    static func decodeURIPayload(_ payload: Data) -> String? {
        guard let code = payload.first else { return nil }
        let remainderData = payload.dropFirst()
        let remainder = String(data: remainderData, encoding: .utf8) ?? ""
        return uriPrefixString(for: code) + remainder
    }

    /// Builds display records from raw NDEF type name / type / payload bytes.
    static func decodeRecord(
        typeNameFormatRawValue: UInt8,
        type: Data,
        payload: Data
    ) -> NFCNDEFDecodedRecord {
        // NFCTypeNameFormat.nfcWellKnown.rawValue == 1
        let isWellKnown = typeNameFormatRawValue == 1
        let typeString = String(data: type, encoding: .utf8)
            ?? type.map { String(format: "%02X", $0) }.joined()

        if isWellKnown, typeString == "T", let decoded = decodeTextPayload(payload) {
            let language = decoded.languageCode.isEmpty ? "" : " (\(decoded.languageCode))"
            return NFCNDEFDecodedRecord(typeLabel: "Text\(language)", body: decoded.text)
        }
        if isWellKnown, typeString == "U", let url = decodeURIPayload(payload) {
            return NFCNDEFDecodedRecord(typeLabel: "URL", body: url)
        }
        if payload.isEmpty {
            return NFCNDEFDecodedRecord(
                typeLabel: typeString.isEmpty ? "Empty" : typeString,
                body: "(no payload)"
            )
        }
        if let utf8 = String(data: payload, encoding: .utf8), !utf8.isEmpty {
            return NFCNDEFDecodedRecord(
                typeLabel: typeString.isEmpty ? "Record" : typeString,
                body: utf8
            )
        }
        let hex = payload.prefix(64).map { String(format: "%02X", $0) }.joined(separator: " ")
        let suffix = payload.count > 64 ? "…" : ""
        return NFCNDEFDecodedRecord(
            typeLabel: typeString.isEmpty ? "Binary" : typeString,
            body: hex + suffix
        )
    }

    /// Joins decoded records into the multiline status string shown after a read.
    static func summary(for records: [NFCNDEFDecodedRecord]) -> String {
        if records.isEmpty {
            return "Tag has no NDEF records."
        }
        return records.enumerated().map { index, record in
            "\(index + 1). \(record.typeLabel)\n\(record.body)"
        }.joined(separator: "\n\n")
    }

    // MARK: - URI abbreviation table (NFC Forum RTD-URI)

    /// Longest-first so `https://www.` wins over `https://`.
    private static let uriPrefixesLongestFirst: [(UInt8, String)] = [
        (0x07, "ftp://anonymous:anonymous@"),
        (0x02, "https://www."),
        (0x01, "http://www."),
        (0x08, "ftp://ftp."),
        (0x1E, "urn:epc:id:"),
        (0x1F, "urn:epc:tag:"),
        (0x20, "urn:epc:pat:"),
        (0x21, "urn:epc:raw:"),
        (0x09, "ftps://"),
        (0x0A, "sftp://"),
        (0x0B, "smb://"),
        (0x0C, "nfs://"),
        (0x0D, "ftp://"),
        (0x0E, "dav://"),
        (0x10, "telnet://"),
        (0x12, "rtsp://"),
        (0x18, "btspp://"),
        (0x19, "btl2cap://"),
        (0x1A, "btgoep://"),
        (0x1B, "tcpobex://"),
        (0x1C, "irdaobex://"),
        (0x1D, "file://"),
        (0x22, "urn:epc:"),
        (0x23, "urn:nfc:"),
        (0x03, "http://"),
        (0x04, "https://"),
        (0x06, "mailto:"),
        (0x0F, "news:"),
        (0x11, "imap:"),
        (0x14, "pop:"),
        (0x15, "sip:"),
        (0x16, "sips:"),
        (0x17, "tftp:"),
        (0x05, "tel:"),
        (0x13, "urn:"),
    ]

    private static func uriPrefix(for urlString: String) -> (UInt8, String) {
        for (code, prefix) in uriPrefixesLongestFirst where urlString.hasPrefix(prefix) {
            return (code, String(urlString.dropFirst(prefix.count)))
        }
        return (0x00, urlString)
    }

    private static func uriPrefixString(for code: UInt8) -> String {
        uriPrefixesLongestFirst.first(where: { $0.0 == code })?.1 ?? ""
    }
}

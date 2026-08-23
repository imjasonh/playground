import XCTest
@testable import Playground

final class NFCNDEFCodecTests: XCTestCase {
    func testValidationRejectsEmptyDraft() {
        let draft = NFCNDEFWriteDraft(kind: .text, text: "   ")
        XCTAssertEqual(NFCNDEFCodec.validationError(for: draft), "Enter text or a URL to write.")
    }

    func testValidationRejectsBogusURL() {
        XCTAssertEqual(
            NFCNDEFCodec.validationError(for: NFCNDEFWriteDraft(kind: .url, text: "not a url")),
            "That does not look like a valid URL."
        )
        XCTAssertEqual(
            NFCNDEFCodec.validationError(for: NFCNDEFWriteDraft(kind: .url, text: "hello")),
            "That does not look like a valid URL."
        )
    }

    func testValidationAcceptsTextAndURL() {
        XCTAssertNil(NFCNDEFCodec.validationError(for: NFCNDEFWriteDraft(kind: .text, text: "hello")))
        XCTAssertNil(
            NFCNDEFCodec.validationError(
                for: NFCNDEFWriteDraft(kind: .url, text: "https://example.com/path")
            )
        )
    }

    func testTextPayloadRoundTrip() {
        let payload = NFCNDEFCodec.encodeTextPayload(text: "Hello NFC", languageCode: "en")
        let decoded = NFCNDEFCodec.decodeTextPayload(payload)
        XCTAssertEqual(decoded?.languageCode, "en")
        XCTAssertEqual(decoded?.text, "Hello NFC")
    }

    func testDecodeUTF16TextPayload() {
        // Status: UTF-16 flag + language length 2 ("en"), then BE "Hi"
        var payload = Data([0x82])
        payload.append(Data("en".utf8))
        payload.append(contentsOf: [0x00, 0x48, 0x00, 0x69]) // "Hi" UTF-16 BE
        let decoded = NFCNDEFCodec.decodeTextPayload(payload)
        XCTAssertEqual(decoded?.languageCode, "en")
        XCTAssertEqual(decoded?.text, "Hi")
    }

    func testURIPayloadRoundTripHTTPS() {
        let original = "https://example.com/nfc"
        let payload = NFCNDEFCodec.encodeURIPayload(urlString: original)
        XCTAssertNotNil(payload)
        // Abbreviation code 0x04 = "https://"
        XCTAssertEqual(payload?.first, 0x04)
        XCTAssertEqual(NFCNDEFCodec.decodeURIPayload(payload!), original)
    }

    func testURIPayloadPrefersLongestPrefix() {
        let original = "https://www.example.com"
        let payload = NFCNDEFCodec.encodeURIPayload(urlString: original)!
        // 0x02 = "https://www." beats 0x04 = "https://"
        XCTAssertEqual(payload.first, 0x02)
        XCTAssertEqual(NFCNDEFCodec.decodeURIPayload(payload), original)
    }

    func testDecodeWellKnownTextRecord() {
        let payload = NFCNDEFCodec.encodeTextPayload(text: "tag body", languageCode: "en")
        let record = NFCNDEFCodec.decodeRecord(
            typeNameFormatRawValue: 1,
            type: Data("T".utf8),
            payload: payload
        )
        XCTAssertEqual(record.typeLabel, "Text (en)")
        XCTAssertEqual(record.body, "tag body")
    }

    func testDecodeWellKnownURLRecord() {
        let payload = NFCNDEFCodec.encodeURIPayload(urlString: "https://example.com")!
        let record = NFCNDEFCodec.decodeRecord(
            typeNameFormatRawValue: 1,
            type: Data("U".utf8),
            payload: payload
        )
        XCTAssertEqual(record.typeLabel, "URL")
        XCTAssertEqual(record.body, "https://example.com")
    }

    func testSummaryFormatsRecords() {
        let records = [
            NFCNDEFDecodedRecord(typeLabel: "Text (en)", body: "one"),
            NFCNDEFDecodedRecord(typeLabel: "URL", body: "https://example.com"),
        ]
        let summary = NFCNDEFCodec.summary(for: records)
        XCTAssertTrue(summary.contains("1. Text (en)"))
        XCTAssertTrue(summary.contains("one"))
        XCTAssertTrue(summary.contains("2. URL"))
        XCTAssertTrue(summary.contains("https://example.com"))
    }

    func testSummaryEmpty() {
        XCTAssertEqual(NFCNDEFCodec.summary(for: []), "Tag has no NDEF records.")
    }

    func testNDEFRecordsMatchRequiresIdenticalSnapshots() {
        let text = NFCNDEFRecordSnapshot(
            typeNameFormatRawValue: 1,
            type: Data("T".utf8),
            payload: NFCNDEFCodec.encodeTextPayload(text: "hello", languageCode: "en")
        )
        let otherText = NFCNDEFRecordSnapshot(
            typeNameFormatRawValue: 1,
            type: Data("T".utf8),
            payload: NFCNDEFCodec.encodeTextPayload(text: "other", languageCode: "en")
        )
        let url = NFCNDEFRecordSnapshot(
            typeNameFormatRawValue: 1,
            type: Data("U".utf8),
            payload: NFCNDEFCodec.encodeURIPayload(urlString: "https://example.com")!
        )

        XCTAssertTrue(NFCNDEFCodec.ndefRecordsMatch([text], [text]))
        XCTAssertFalse(NFCNDEFCodec.ndefRecordsMatch([text], [otherText]))
        XCTAssertFalse(NFCNDEFCodec.ndefRecordsMatch([text], [url]))
        XCTAssertFalse(NFCNDEFCodec.ndefRecordsMatch([text], []))
        XCTAssertFalse(NFCNDEFCodec.ndefRecordsMatch([text], [text, text]))
        XCTAssertTrue(NFCNDEFCodec.ndefRecordsMatch([], []))
    }
}

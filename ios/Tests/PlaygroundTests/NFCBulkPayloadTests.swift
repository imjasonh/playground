import XCTest
@testable import Playground
import CoreNFC

final class NFCBulkPayloadTests: XCTestCase {
    func testEmptyDraftIsInvalid() {
        let draft = NFCBulkPayloadDraft(kind: .text, text: "   ")
        XCTAssertTrue(draft.isEmpty)
        XCTAssertFalse(draft.isValid)
        XCTAssertEqual(draft.validationError, "Enter a payload before starting.")
    }

    func testTextDraftIsValid() {
        let draft = NFCBulkPayloadDraft(kind: .text, text: " Hello ")
        XCTAssertEqual(draft.trimmedText, "Hello")
        XCTAssertTrue(draft.isValid)
        XCTAssertNil(draft.validationError)
    }

    func testURLNormalizationAddsHTTPS() {
        XCTAssertEqual(
            NFCBulkPayloadDraft.normalizeURLString("example.com/path"),
            "https://example.com/path"
        )
    }

    func testURLNormalizationKeepsHTTP() {
        XCTAssertEqual(
            NFCBulkPayloadDraft.normalizeURLString("http://example.com"),
            "http://example.com"
        )
    }

    func testURLNormalizationRejectsNonHTTPSchemes() {
        XCTAssertNil(NFCBulkPayloadDraft.normalizeURLString("ftp://example.com"))
        XCTAssertNil(NFCBulkPayloadDraft.normalizeURLString("mailto:hi@example.com"))
    }

    func testURLDraftValidation() {
        var draft = NFCBulkPayloadDraft(kind: .url, text: "ftp://files.example")
        XCTAssertFalse(draft.isValid)

        draft.text = "example.com"
        XCTAssertTrue(draft.isValid)
        XCTAssertEqual(draft.normalizedURLString, "https://example.com")
    }

    func testBuildsTextNDEFMessage() throws {
        let draft = NFCBulkPayloadDraft(kind: .text, text: "bulk write")
        let message = try NFCBulkNDEFBuilder.message(from: draft)
        XCTAssertEqual(message.records.count, 1)
        let (text, locale) = message.records[0].wellKnownTypeTextPayload()
        XCTAssertEqual(text, "bulk write")
        XCTAssertEqual(locale?.languageCode, "en")
    }

    func testBuildsURLNDEFMessage() throws {
        let draft = NFCBulkPayloadDraft(kind: .url, text: "example.com/nfc")
        let message = try NFCBulkNDEFBuilder.message(from: draft)
        XCTAssertEqual(message.records.count, 1)
        let url = message.records[0].wellKnownTypeURIPayload()
        XCTAssertEqual(url?.absoluteString, "https://example.com/nfc")
    }

    func testBuilderRejectsEmptyPayload() {
        let draft = NFCBulkPayloadDraft(kind: .text, text: "")
        XCTAssertThrowsError(try NFCBulkNDEFBuilder.message(from: draft)) { error in
            XCTAssertEqual(error as? NFCBulkNDEFBuilder.BuildError, .emptyPayload)
        }
    }

    func testBuilderRejectsInvalidURL() {
        let draft = NFCBulkPayloadDraft(kind: .url, text: "ftp://nope.example")
        XCTAssertThrowsError(try NFCBulkNDEFBuilder.message(from: draft)) { error in
            XCTAssertEqual(error as? NFCBulkNDEFBuilder.BuildError, .invalidURL)
        }
    }

    func testEstimatedByteCountPositive() {
        let text = NFCBulkPayloadDraft(kind: .text, text: "hi")
        XCTAssertGreaterThan(NFCBulkNDEFBuilder.estimatedByteCount(of: text), 0)

        let url = NFCBulkPayloadDraft(kind: .url, text: "https://example.com")
        XCTAssertGreaterThan(NFCBulkNDEFBuilder.estimatedByteCount(of: url), 0)
    }
}

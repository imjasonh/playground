import XCTest
@testable import Playground

final class NFCTagScanFormatterTests: XCTestCase {
    func testUIDHexUsesColonSeparatedUppercase() {
        let data = Data([0x04, 0xD3, 0xE8, 0x85, 0x37, 0x02, 0x89])
        XCTAssertEqual(NFCTagScanFormatter.uidHex(data), "04:D3:E8:85:37:02:89")
    }

    func testEmptyNDEFErrorCodeMatchesCoreNFCZeroLength() {
        XCTAssertTrue(
            NFCTagScanFormatter.isEmptyNDEFErrorCode(
                NFCTagScanFormatter.zeroLengthNDEFMessageErrorCode
            )
        )
        XCTAssertFalse(NFCTagScanFormatter.isEmptyNDEFErrorCode(0))
        XCTAssertFalse(NFCTagScanFormatter.isEmptyNDEFErrorCode(100))
    }

    func testBlankTagSummaryIncludesWritableCapacityAndIdentity() {
        let summary = NFCTagScanFormatter.blankTagSummary(
            writable: true,
            capacity: 492,
            uid: "04:D3:E8:85:37:02:89",
            family: "ISO 14443 (NTAG / MiFare)"
        )
        XCTAssertTrue(summary.contains("Blank NDEF tag (writable)"))
        XCTAssertTrue(summary.contains("NDEF capacity: 492 bytes"))
        XCTAssertTrue(summary.contains("Type: ISO 14443 (NTAG / MiFare)"))
        XCTAssertTrue(summary.contains("UID: 04:D3:E8:85:37:02:89"))
    }

    func testBlankTagSummaryReadOnlyOmitsZeroCapacity() {
        let summary = NFCTagScanFormatter.blankTagSummary(
            writable: false,
            capacity: 0,
            uid: nil,
            family: nil
        )
        XCTAssertEqual(summary, "Blank NDEF tag (read-only)")
    }

    func testNonNDEFSummaryPointsAtWrite() {
        let summary = NFCTagScanFormatter.nonNDEFSummary(
            uid: "AA:BB",
            family: "ISO 15693"
        )
        XCTAssertTrue(summary.contains("no NDEF message"))
        XCTAssertTrue(summary.contains("UID: AA:BB"))
        XCTAssertTrue(summary.contains("Use Write"))
    }

    func testRecordsSummaryAppendsIdentity() {
        let summary = NFCTagScanFormatter.recordsSummary(
            "1. Text (en)\nhello",
            uid: "01:02",
            family: "FeliCa"
        )
        XCTAssertTrue(summary.hasPrefix("1. Text (en)"))
        XCTAssertTrue(summary.contains("Type: FeliCa"))
        XCTAssertTrue(summary.contains("UID: 01:02"))
    }
}

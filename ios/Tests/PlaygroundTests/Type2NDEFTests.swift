import XCTest
@testable import Playground

final class Type2NDEFTests: XCTestCase {
    func testWellKnownTextRecordRoundTripThroughTLV() {
        let payload = NFCNDEFCodec.encodeTextPayload(text: "hi", languageCode: "en")
        let ndef = Type2NDEF.wellKnownRecord(typeAscii: "T", payload: payload)
        let tlv = Type2NDEF.wrapTLV(ndef)
        XCTAssertEqual(tlv.first, 0x03)
        XCTAssertEqual(tlv[1], UInt8(ndef.count))
        XCTAssertEqual(tlv.last, 0xFE)

        let extracted = Type2NDEF.extractNDEFMessage(fromUserMemory: tlv)
        XCTAssertEqual(extracted, ndef)
    }

    func testExtractSkipsNullAndLockTLVs() {
        let payload = NFCNDEFCodec.encodeTextPayload(text: "x", languageCode: "en")
        let ndef = Type2NDEF.wellKnownRecord(typeAscii: "T", payload: payload)
        // NULL TLV (0x00), Lock Control TLV (0x01, len 3), then NDEF TLV.
        var memory = Data([0x00, 0x01, 0x03, 0xA0, 0x0C, 0x34])
        memory.append(Type2NDEF.wrapTLV(ndef))
        XCTAssertEqual(Type2NDEF.extractNDEFMessage(fromUserMemory: memory), ndef)
    }

    func testCapabilityContainerDetectAndBuild() {
        XCTAssertTrue(Type2NDEF.hasNDEFCapabilityContainer(Data([0xE1, 0x10, 0x3E, 0x00])))
        XCTAssertFalse(Type2NDEF.hasNDEFCapabilityContainer(Data([0x00, 0x00, 0x00, 0x00])))
        XCTAssertEqual(
            Type2NDEF.capabilityContainer(ndefCapacity: 496),
            Data([0xE1, 0x10, 0x3E, 0x00])
        )
    }

    func testPagesPadsLastPage() {
        let pages = Type2NDEF.pages(from: Data([1, 2, 3, 4, 5]))
        XCTAssertEqual(pages.count, 2)
        XCTAssertEqual(pages[0], [1, 2, 3, 4])
        XCTAssertEqual(pages[1], [5, 0, 0, 0])
    }

    func testCommandPackets() {
        XCTAssertEqual(Type2NDEF.readCommandPacket(page: 4), Data([0x30, 0x04]))
        XCTAssertEqual(
            Type2NDEF.writeCommandPacket(page: 4, bytes: [0x03, 0x01, 0x02, 0xFE]),
            Data([0xA2, 0x04, 0x03, 0x01, 0x02, 0xFE])
        )
    }

    func testNDEFMessageAndSnapshotsForDraft() {
        let textDraft = NFCNDEFWriteDraft(kind: .text, text: "hello")
        let ndef = Type2NDEF.ndefMessage(for: textDraft)!
        let snaps = Type2NDEF.snapshots(for: textDraft)!
        XCTAssertEqual(ndef[0], 0xD1)
        XCTAssertEqual(String(data: Data(ndef[3..<4]), encoding: .utf8), "T")
        XCTAssertEqual(snaps.count, 1)
        XCTAssertEqual(snaps[0].type, Data("T".utf8))
        XCTAssertEqual(
            NFCNDEFCodec.decodeTextPayload(snaps[0].payload)?.text,
            "hello"
        )

        let urlDraft = NFCNDEFWriteDraft(kind: .url, text: "https://example.com")
        let urlNDEF = Type2NDEF.ndefMessage(for: urlDraft)!
        XCTAssertEqual(String(data: Data(urlNDEF[3..<4]), encoding: .utf8), "U")
    }
}

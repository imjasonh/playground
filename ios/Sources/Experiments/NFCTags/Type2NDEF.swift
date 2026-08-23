import Foundation

/// NFC Forum Type 2 tag (NTAG / Ultralight) NDEF framing helpers.
///
/// Memory layout used here: capability container on page 3, NDEF TLV starting
/// at page 4. READ (0x30) returns 16 bytes; WRITE (0xA2) writes one 4-byte page.
enum Type2NDEF {
    static let capabilityContainerPage: UInt8 = 3
    static let ndefTLVStartPage: UInt8 = 4
    static let readCommand: UInt8 = 0x30
    static let writeCommand: UInt8 = 0xA2
    static let ndefTLVType: UInt8 = 0x03
    static let terminatorTLV: UInt8 = 0xFE
    static let magicE1: UInt8 = 0xE1

    /// Builds a single short well-known NDEF record (MB+ME, SR, TNF=well-known).
    static func wellKnownRecord(typeAscii: String, payload: Data) -> Data {
        let typeData = Data(typeAscii.utf8)
        precondition(typeData.count <= 255)
        precondition(payload.count <= 255)
        // 0xD1 = MB|ME|SR|TNF_well_known
        var record = Data([0xD1, UInt8(typeData.count), UInt8(payload.count)])
        record.append(typeData)
        record.append(payload)
        return record
    }

    /// Wraps an NDEF message in a Type 2 NDEF Message TLV plus terminator.
    static func wrapTLV(_ ndefMessage: Data) -> Data {
        var tlv = Data()
        tlv.append(ndefTLVType)
        if ndefMessage.count < 0xFF {
            tlv.append(UInt8(ndefMessage.count))
        } else {
            tlv.append(0xFF)
            tlv.append(UInt8((ndefMessage.count >> 8) & 0xFF))
            tlv.append(UInt8(ndefMessage.count & 0xFF))
        }
        tlv.append(ndefMessage)
        tlv.append(terminatorTLV)
        return tlv
    }

    /// Extracts the NDEF message bytes from Type 2 user memory (page 4 onward).
    static func extractNDEFMessage(fromUserMemory memory: Data) -> Data? {
        var index = 0
        while index < memory.count {
            let type = memory[index]
            index += 1
            if type == 0x00 {
                // NULL TLV — skip one byte already consumed as type; no length.
                continue
            }
            if type == terminatorTLV {
                return nil
            }
            guard index < memory.count else { return nil }
            let length: Int
            let firstLen = memory[index]
            index += 1
            if firstLen == 0xFF {
                guard index + 1 < memory.count else { return nil }
                length = (Int(memory[index]) << 8) | Int(memory[index + 1])
                index += 2
            } else {
                length = Int(firstLen)
            }
            guard index + length <= memory.count else { return nil }
            let value = memory.subdata(in: index..<(index + length))
            index += length
            if type == ndefTLVType {
                return value
            }
            // Skip Lock Control / Memory Control / proprietary TLVs.
        }
        return nil
    }

    /// True when page-3 capability container claims NDEF mapping (magic 0xE1).
    static func hasNDEFCapabilityContainer(_ page3: Data) -> Bool {
        guard page3.count >= 4 else { return false }
        return page3[0] == magicE1
    }

    /// Builds a writable NDEF capability container for `ndefCapacity` user bytes.
    static func capabilityContainer(ndefCapacity: Int) -> Data {
        let sizeByte = UInt8(min(255, max(1, ndefCapacity / 8)))
        // E1 | version 1.0 | size/8 | read/write free
        return Data([magicE1, 0x10, sizeByte, 0x00])
    }

    /// Packs bytes into 4-byte pages (pads the last page with 0x00).
    static func pages(from bytes: Data) -> [[UInt8]] {
        var result: [[UInt8]] = []
        var offset = 0
        while offset < bytes.count {
            var page = [UInt8](repeating: 0, count: 4)
            let end = min(offset + 4, bytes.count)
            for i in offset..<end {
                page[i - offset] = bytes[i]
            }
            result.append(page)
            offset += 4
        }
        return result
    }

    /// Command packet for READ starting at `page` (response is 16 bytes).
    static func readCommandPacket(page: UInt8) -> Data {
        Data([readCommand, page])
    }

    /// Command packet for WRITE of one 4-byte page.
    static func writeCommandPacket(page: UInt8, bytes: [UInt8]) -> Data {
        precondition(bytes.count == 4)
        return Data([writeCommand, page]) + Data(bytes)
    }

    /// NDEF message bytes for a text or URL draft using `NFCNDEFCodec` payloads.
    static func ndefMessage(for draft: NFCNDEFWriteDraft) -> Data? {
        let trimmed = draft.text.trimmingCharacters(in: .whitespacesAndNewlines)
        switch draft.kind {
        case .text:
            let payload = NFCNDEFCodec.encodeTextPayload(text: trimmed, languageCode: "en")
            return wellKnownRecord(typeAscii: "T", payload: payload)
        case .url:
            guard let payload = NFCNDEFCodec.encodeURIPayload(urlString: trimmed) else {
                return nil
            }
            return wellKnownRecord(typeAscii: "U", payload: payload)
        }
    }

    /// Snapshot list matching `ndefMessage(for:)` for write verify comparisons.
    static func snapshots(for draft: NFCNDEFWriteDraft) -> [NFCNDEFRecordSnapshot]? {
        let trimmed = draft.text.trimmingCharacters(in: .whitespacesAndNewlines)
        switch draft.kind {
        case .text:
            return [
                NFCNDEFRecordSnapshot(
                    typeNameFormatRawValue: 1,
                    type: Data("T".utf8),
                    payload: NFCNDEFCodec.encodeTextPayload(text: trimmed, languageCode: "en")
                ),
            ]
        case .url:
            guard let payload = NFCNDEFCodec.encodeURIPayload(urlString: trimmed) else {
                return nil
            }
            return [
                NFCNDEFRecordSnapshot(
                    typeNameFormatRawValue: 1,
                    type: Data("U".utf8),
                    payload: payload
                ),
            ]
        }
    }
}

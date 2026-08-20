import Foundation

/// Builds a ZIP archive with stored (uncompressed) entries. Used so bulk ride
/// export can hand the Files picker one `.zip` instead of many loose `.jsonl`
/// files.
enum RideZipArchive {
    /// Creates a ZIP from `(filename, bytes)` pairs. Filenames must be relative
    /// path segments without leading `/` or `..`.
    static func data(entries: [(name: String, data: Data)]) throws -> Data {
        guard !entries.isEmpty else {
            throw ArchiveError.emptyArchive
        }

        var localChunks: [Data] = []
        localChunks.reserveCapacity(entries.count)
        var centralChunks: [Data] = []
        centralChunks.reserveCapacity(entries.count)
        var offset: UInt32 = 0

        for entry in entries {
            let name = try normalizedFilename(entry.name)
            let nameData = Data(name.utf8)
            guard nameData.count <= Int(UInt16.max) else {
                throw ArchiveError.filenameTooLong
            }

            let payload = entry.data
            let crc = crc32(for: payload)
            let size = UInt32(payload.count)
            let localHeader = localFileHeader(
                nameData: nameData,
                crc: crc,
                size: size
            )
            localChunks.append(localHeader)
            localChunks.append(payload)

            centralChunks.append(centralDirectoryHeader(
                nameData: nameData,
                crc: crc,
                size: size,
                localHeaderOffset: offset
            ))
            offset += UInt32(localHeader.count + payload.count)
        }

        var archive = Data()
        let localSize = localChunks.reduce(0) { $0 + $1.count }
        let centralSize = centralChunks.reduce(0) { $0 + $1.count }
        archive.reserveCapacity(localSize + centralSize + 22)

        for chunk in localChunks {
            archive.append(chunk)
        }
        let centralDirectoryOffset = UInt32(archive.count)
        for chunk in centralChunks {
            archive.append(chunk)
        }
        archive.append(endOfCentralDirectory(
            entryCount: UInt16(entries.count),
            centralDirectorySize: UInt32(centralSize),
            centralDirectoryOffset: centralDirectoryOffset
        ))
        return archive
    }

    enum ArchiveError: Error {
        case emptyArchive
        case filenameTooLong
        case invalidFilename
    }

    private static func normalizedFilename(_ name: String) throws -> String {
        let trimmed = name.trimmingCharacters(in: CharacterSet(charactersIn: "/"))
        guard !trimmed.isEmpty,
              !trimmed.contains("\0"),
              !trimmed.split(separator: "/").contains("..") else {
            throw ArchiveError.invalidFilename
        }
        return trimmed
    }

    /// IEEE CRC-32 (ISO 3309 / ZIP / PNG), computed without linking zlib.
    private static func crc32(for data: Data) -> UInt32 {
        var crc: UInt32 = 0xffff_ffff
        for byte in data {
            let index = Int((crc ^ UInt32(byte)) & 0xff)
            crc = (crc >> 8) ^ crc32Table[index]
        }
        return crc ^ 0xffff_ffff
    }

    private static let crc32Table: [UInt32] = {
        (0..<256).map { index -> UInt32 in
            var crc = UInt32(index)
            for _ in 0..<8 {
                if crc & 1 != 0 {
                    crc = (crc >> 1) ^ 0xedb8_8320
                } else {
                    crc >>= 1
                }
            }
            return crc
        }
    }()

    private static func localFileHeader(nameData: Data, crc: UInt32, size: UInt32) -> Data {
        var header = Data(capacity: 30 + nameData.count)
        header.appendUInt32LE(0x0403_4b50) // local file header signature
        header.appendUInt16LE(20) // version needed to extract
        header.appendUInt16LE(0) // general purpose bit flag
        header.appendUInt16LE(0) // compression method = store
        header.appendUInt16LE(0) // last mod file time
        header.appendUInt16LE(0) // last mod file date
        header.appendUInt32LE(crc)
        header.appendUInt32LE(size) // compressed size
        header.appendUInt32LE(size) // uncompressed size
        header.appendUInt16LE(UInt16(nameData.count))
        header.appendUInt16LE(0) // extra field length
        header.append(nameData)
        return header
    }

    private static func centralDirectoryHeader(
        nameData: Data,
        crc: UInt32,
        size: UInt32,
        localHeaderOffset: UInt32
    ) -> Data {
        var header = Data(capacity: 46 + nameData.count)
        header.appendUInt32LE(0x0201_4b50) // central file header signature
        header.appendUInt16LE(20) // version made by
        header.appendUInt16LE(20) // version needed to extract
        header.appendUInt16LE(0) // general purpose bit flag
        header.appendUInt16LE(0) // compression method = store
        header.appendUInt16LE(0) // last mod file time
        header.appendUInt16LE(0) // last mod file date
        header.appendUInt32LE(crc)
        header.appendUInt32LE(size) // compressed size
        header.appendUInt32LE(size) // uncompressed size
        header.appendUInt16LE(UInt16(nameData.count))
        header.appendUInt16LE(0) // extra field length
        header.appendUInt16LE(0) // file comment length
        header.appendUInt16LE(0) // disk number start
        header.appendUInt16LE(0) // internal file attributes
        header.appendUInt32LE(0) // external file attributes
        header.appendUInt32LE(localHeaderOffset)
        header.append(nameData)
        return header
    }

    private static func endOfCentralDirectory(
        entryCount: UInt16,
        centralDirectorySize: UInt32,
        centralDirectoryOffset: UInt32
    ) -> Data {
        var trailer = Data(capacity: 22)
        trailer.appendUInt32LE(0x0605_4b50) // end of central dir signature
        trailer.appendUInt16LE(0) // number of this disk
        trailer.appendUInt16LE(0) // disk where central directory starts
        trailer.appendUInt16LE(entryCount) // entries on this disk
        trailer.appendUInt16LE(entryCount) // total entries
        trailer.appendUInt32LE(centralDirectorySize)
        trailer.appendUInt32LE(centralDirectoryOffset)
        trailer.appendUInt16LE(0) // comment length
        return trailer
    }
}

private extension Data {
    mutating func appendUInt16LE(_ value: UInt16) {
        var littleEndian = value.littleEndian
        Swift.withUnsafeBytes(of: &littleEndian) { append(contentsOf: $0) }
    }

    mutating func appendUInt32LE(_ value: UInt32) {
        var littleEndian = value.littleEndian
        Swift.withUnsafeBytes(of: &littleEndian) { append(contentsOf: $0) }
    }
}

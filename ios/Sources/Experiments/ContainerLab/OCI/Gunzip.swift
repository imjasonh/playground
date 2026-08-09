import Compression
import Foundation

enum GzipError: Error, LocalizedError {
    case notGzip
    case truncated
    case unsupportedCompressionMethod(UInt8)
    case decompressionFailed

    var errorDescription: String? {
        switch self {
        case .notGzip:
            return "Blob is not gzip data"
        case .truncated:
            return "Gzip data is truncated"
        case .unsupportedCompressionMethod(let method):
            return "Unsupported gzip compression method \(method)"
        case .decompressionFailed:
            return "Gzip decompression failed"
        }
    }
}

/// Gzip decoding for image layers.
///
/// Layers arrive gzip-compressed; decompressing them natively (rather than
/// inside the wasm guest, which container2wasm documents as very slow) is one
/// of the main reasons the native side does the pulling. Apple's `Compression`
/// framework speaks raw DEFLATE, so the gzip envelope is parsed here.
enum Gunzip {
    static func isGzip(_ data: Data) -> Bool {
        guard data.count >= 2 else { return false }
        let bytes = [UInt8](data.prefix(2))
        return bytes[0] == 0x1f && bytes[1] == 0x8b
    }

    static func decompress(_ data: Data) throws -> Data {
        let bytes = [UInt8](data)
        // 10-byte header + 8-byte trailer is the smallest possible member.
        guard bytes.count >= 18 else { throw GzipError.truncated }
        guard bytes[0] == 0x1f, bytes[1] == 0x8b else { throw GzipError.notGzip }
        guard bytes[2] == 8 else { throw GzipError.unsupportedCompressionMethod(bytes[2]) }

        let flags = bytes[3]
        var offset = 10

        if flags & 0x04 != 0 { // FEXTRA
            guard offset + 2 <= bytes.count else { throw GzipError.truncated }
            let extraLength = Int(bytes[offset]) | (Int(bytes[offset + 1]) << 8)
            offset += 2 + extraLength
        }
        if flags & 0x08 != 0 { // FNAME
            offset = try skipCString(bytes, from: offset)
        }
        if flags & 0x10 != 0 { // FCOMMENT
            offset = try skipCString(bytes, from: offset)
        }
        if flags & 0x02 != 0 { // FHCRC
            offset += 2
        }

        let payloadEnd = bytes.count - 8
        guard offset < payloadEnd else { throw GzipError.truncated }

        let isize = Int(bytes[bytes.count - 4])
            | (Int(bytes[bytes.count - 3]) << 8)
            | (Int(bytes[bytes.count - 2]) << 16)
            | (Int(bytes[bytes.count - 1]) << 24)

        return try inflateRaw(Array(bytes[offset..<payloadEnd]), hint: isize)
    }

    private static func skipCString(_ bytes: [UInt8], from start: Int) throws -> Int {
        var index = start
        while index < bytes.count {
            if bytes[index] == 0 { return index + 1 }
            index += 1
        }
        throw GzipError.truncated
    }

    private static func inflateRaw(_ input: [UInt8], hint: Int) throws -> Data {
        guard !input.isEmpty else { return Data() }

        let bufferSize = 128 * 1024
        let destination = UnsafeMutablePointer<UInt8>.allocate(capacity: bufferSize)
        defer { destination.deallocate() }

        var stream = compression_stream(
            dst_ptr: destination,
            dst_size: bufferSize,
            src_ptr: destination,
            src_size: 0,
            state: nil
        )
        guard compression_stream_init(&stream, COMPRESSION_STREAM_DECODE, COMPRESSION_ZLIB)
            == COMPRESSION_STATUS_OK else {
            throw GzipError.decompressionFailed
        }
        defer { compression_stream_destroy(&stream) }

        var output = Data()
        output.reserveCapacity(hint > 0 ? hint : input.count * 4)
        var failure: Error?

        input.withUnsafeBufferPointer { buffer in
            guard let base = buffer.baseAddress else { return }
            stream.src_ptr = base
            stream.src_size = buffer.count

            let flags = Int32(COMPRESSION_STREAM_FINALIZE.rawValue)
            var finished = false
            while !finished {
                stream.dst_ptr = destination
                stream.dst_size = bufferSize
                let status = compression_stream_process(&stream, flags)
                let produced = bufferSize - stream.dst_size
                if produced > 0 {
                    output.append(destination, count: produced)
                }
                switch status {
                case COMPRESSION_STATUS_END:
                    finished = true
                case COMPRESSION_STATUS_OK:
                    // No progress and nothing left to read means a malformed stream;
                    // bail instead of spinning.
                    if produced == 0 && stream.src_size == 0 {
                        failure = GzipError.decompressionFailed
                        finished = true
                    }
                default:
                    failure = GzipError.decompressionFailed
                    finished = true
                }
            }
        }

        if let failure { throw failure }
        return output
    }
}

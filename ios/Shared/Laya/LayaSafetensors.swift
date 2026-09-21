import Foundation

/// IEEE binary16 conversions without the `Float16` type, so the same code
/// compiles for every simulator architecture.
enum LayaHalf {
    /// Round-to-nearest-even conversion.
    static func encode(_ value: Float) -> UInt16 {
        let bits = value.bitPattern
        let sign = UInt16((bits >> 16) & 0x8000)
        let exponentBits = Int((bits >> 23) & 0xFF)
        let mantissa = bits & 0x7F_FFFF

        if exponentBits == 0xFF {
            // Inf or NaN.
            return sign | 0x7C00 | (mantissa == 0 ? 0 : 0x0200)
        }
        let exponent = exponentBits - 127 + 15
        if exponent >= 0x1F {
            return sign | 0x7C00
        }
        if exponent <= 0 {
            if exponent < -10 {
                return sign // Too small for a half subnormal: signed zero.
            }
            let full = mantissa | 0x80_0000
            let shift = UInt32(14 - exponent)
            var half = UInt16(full >> shift)
            let remainder = full & ((1 << shift) - 1)
            let halfway = UInt32(1) << (shift - 1)
            if remainder > halfway || (remainder == halfway && (half & 1) == 1) {
                half += 1
            }
            return sign | half
        }
        var half = UInt16(exponent << 10) | UInt16(mantissa >> 13)
        let remainder = mantissa & 0x1FFF
        if remainder > 0x1000 || (remainder == 0x1000 && (half & 1) == 1) {
            half += 1 // A carry into the exponent is the correct rounding.
        }
        return sign | half
    }

    static func decode(_ half: UInt16) -> Float {
        let sign = UInt32(half & 0x8000) << 16
        let exponent = UInt32((half >> 10) & 0x1F)
        let mantissa = UInt32(half & 0x03FF)
        if exponent == 0 {
            if mantissa == 0 {
                return Float(bitPattern: sign)
            }
            // Subnormal: normalize.
            var e: UInt32 = 127 - 15 + 1
            var m = mantissa
            while (m & 0x0400) == 0 {
                m <<= 1
                e -= 1
            }
            m &= 0x03FF
            return Float(bitPattern: sign | (e << 23) | (m << 13))
        }
        if exponent == 0x1F {
            return Float(bitPattern: sign | 0x7F80_0000 | (mantissa << 13))
        }
        return Float(bitPattern: sign | ((exponent + 127 - 15) << 23) | (mantissa << 13))
    }

    static func decodeBFloat16(_ value: UInt16) -> Float {
        Float(bitPattern: UInt32(value) << 16)
    }
}

/// Element types this reader converts to `Float`.
enum LayaDType: String, Codable {
    case f32 = "F32"
    case f16 = "F16"
    case bf16 = "BF16"
    case f64 = "F64"

    var byteSize: Int {
        switch self {
        case .f16, .bf16: return 2
        case .f32: return 4
        case .f64: return 8
        }
    }
}

/// One tensor inside a memory-mapped safetensors file. Rows convert lazily so
/// a 256k-row embedding table never has to become `[Float]` in full.
struct LayaTensor {
    let name: String
    let dtype: LayaDType
    let shape: [Int]
    private let data: Data
    private let byteOffset: Int

    init(name: String, dtype: LayaDType, shape: [Int], data: Data, byteOffset: Int) {
        self.name = name
        self.dtype = dtype
        self.shape = shape
        self.data = data
        self.byteOffset = byteOffset
    }

    var elementCount: Int { shape.reduce(1, *) }

    /// Elements `[start, start + count)` in row-major order as `Float`.
    func floats(from start: Int, count: Int) -> [Float] {
        precondition(start >= 0 && start + count <= elementCount, "tensor slice out of range")
        var out = [Float](repeating: 0, count: count)
        let base = byteOffset + start * dtype.byteSize
        data.withUnsafeBytes { raw in
            for i in 0..<count {
                let offset = base + i * dtype.byteSize
                switch dtype {
                case .f32:
                    out[i] = Float(bitPattern: raw.loadUnaligned(fromByteOffset: offset, as: UInt32.self).littleEndian)
                case .f16:
                    out[i] = LayaHalf.decode(raw.loadUnaligned(fromByteOffset: offset, as: UInt16.self).littleEndian)
                case .bf16:
                    out[i] = LayaHalf.decodeBFloat16(raw.loadUnaligned(fromByteOffset: offset, as: UInt16.self).littleEndian)
                case .f64:
                    out[i] = Float(Double(bitPattern: raw.loadUnaligned(fromByteOffset: offset, as: UInt64.self).littleEndian))
                }
            }
        }
        return out
    }

    func floats() -> [Float] {
        floats(from: 0, count: elementCount)
    }

    /// Row `index` of a 2-D tensor.
    func row(_ index: Int) -> [Float] {
        precondition(shape.count == 2, "row() needs a 2-D tensor")
        let width = shape[1]
        return floats(from: index * width, count: width)
    }
}

/// Minimal safetensors reader: 8-byte little-endian header length, JSON
/// header, then the raw tensor buffer.
struct LayaSafetensorsFile {
    private struct Header: Decodable {
        let dtype: String
        let shape: [Int]
        let dataOffsets: [Int]

        enum CodingKeys: String, CodingKey {
            case dtype
            case shape
            case dataOffsets = "data_offsets"
        }
    }

    private let data: Data
    private let headers: [String: Header]
    private let bufferStart: Int

    var tensorNames: [String] { headers.keys.sorted() }

    init(url: URL) throws {
        try self.init(data: try Data(contentsOf: url, options: .mappedIfSafe))
    }

    init(data: Data) throws {
        guard data.count >= 8 else {
            throw LayaError.bundle("safetensors file is shorter than its header length field.")
        }
        let headerLength = Int(data.withUnsafeBytes { $0.loadUnaligned(fromByteOffset: 0, as: UInt64.self).littleEndian })
        guard headerLength > 0, 8 + headerLength <= data.count else {
            throw LayaError.bundle("safetensors header length \(headerLength) exceeds the file.")
        }
        let headerData = data.subdata(in: 8..<(8 + headerLength))
        let raw = try JSONSerialization.jsonObject(with: headerData)
        guard var dictionary = raw as? [String: Any] else {
            throw LayaError.bundle("safetensors header is not a JSON object.")
        }
        dictionary.removeValue(forKey: "__metadata__")
        let encoded = try JSONSerialization.data(withJSONObject: dictionary)
        self.headers = try JSONDecoder().decode([String: Header].self, from: encoded)
        self.data = data
        self.bufferStart = 8 + headerLength
    }

    func tensor(named name: String) throws -> LayaTensor {
        guard let header = headers[name] else {
            throw LayaError.bundle("host_weights.safetensors is missing \(name).")
        }
        guard let dtype = LayaDType(rawValue: header.dtype) else {
            throw LayaError.bundle("\(name) has unsupported dtype \(header.dtype).")
        }
        guard header.dataOffsets.count == 2 else {
            throw LayaError.bundle("\(name) has a malformed data_offsets entry.")
        }
        let start = bufferStart + header.dataOffsets[0]
        let end = bufferStart + header.dataOffsets[1]
        let expectedBytes = header.shape.reduce(1, *) * dtype.byteSize
        guard start >= bufferStart, end <= data.count, end - start == expectedBytes else {
            throw LayaError.bundle("\(name) data offsets do not match its shape.")
        }
        return LayaTensor(name: name, dtype: dtype, shape: header.shape, data: data, byteOffset: start)
    }
}

import Foundation
import WasmKit

/// Bounds-checked, little-endian access to a module's linear memory.
///
/// Every read and write here comes from a pointer the *guest* chose, so
/// nothing may be taken on trust: an out-of-range offset has to become
/// `EFAULT` for the guest rather than a stray read in the app's address space.
/// WasmKit's `withUnsafeMutableBufferPointer(offset:count:)` does no checking
/// of its own, which is why every accessor goes through `checkBounds` first.
///
/// Integers are assembled byte by byte rather than loaded as words: wasm is
/// little-endian regardless of the host, and a guest pointer carries no
/// alignment guarantee.
struct GuestMemoryView {
    let memory: Memory

    /// The memory's current size, which grows as the guest grows it.
    ///
    /// Reading `memory.data` hands back the underlying array, so this is O(1)
    /// — but the reference it briefly holds must not still be alive when
    /// something writes, or copy-on-write would duplicate the whole linear
    /// memory to service a one-byte store. Keeping it to this one expression
    /// is what makes that safe.
    var byteCount: Int { memory.data.count }

    // MARK: - Bytes

    func read(offset: UInt32, count: Int) throws -> [UInt8] {
        guard count > 0 else { return [] }
        try checkBounds(offset: offset, count: count)
        return memory.withUnsafeMutableBufferPointer(offset: UInt(offset), count: count) { raw in
            [UInt8](raw)
        }
    }

    func readData(offset: UInt32, count: Int) throws -> Data {
        guard count > 0 else { return Data() }
        try checkBounds(offset: offset, count: count)
        return memory.withUnsafeMutableBufferPointer(offset: UInt(offset), count: count) { raw in
            Data(raw)
        }
    }

    func write<Bytes: Collection>(_ bytes: Bytes, at offset: UInt32) throws where Bytes.Element == UInt8 {
        let count = bytes.count
        guard count > 0 else { return }
        try checkBounds(offset: offset, count: count)
        memory.withUnsafeMutableBufferPointer(offset: UInt(offset), count: count) { raw in
            raw.copyBytes(from: bytes)
        }
    }

    // MARK: - Integers

    func readUInt16(at offset: UInt32) throws -> UInt16 {
        let bytes = try read(offset: offset, count: 2)
        return UInt16(bytes[0]) | UInt16(bytes[1]) << 8
    }

    func readUInt32(at offset: UInt32) throws -> UInt32 {
        let bytes = try read(offset: offset, count: 4)
        var value: UInt32 = 0
        for index in (0..<4).reversed() {
            value = value << 8 | UInt32(bytes[index])
        }
        return value
    }

    func readUInt64(at offset: UInt32) throws -> UInt64 {
        let bytes = try read(offset: offset, count: 8)
        var value: UInt64 = 0
        for index in (0..<8).reversed() {
            value = value << 8 | UInt64(bytes[index])
        }
        return value
    }

    func writeUInt16(_ value: UInt16, at offset: UInt32) throws {
        try write([UInt8(value & 0xff), UInt8(value >> 8 & 0xff)], at: offset)
    }

    func writeUInt32(_ value: UInt32, at offset: UInt32) throws {
        try write((0..<4).map { UInt8(value >> (8 * $0) & 0xff) }, at: offset)
    }

    func writeUInt64(_ value: UInt64, at offset: UInt32) throws {
        try write((0..<8).map { UInt8(value >> (8 * $0) & 0xff) }, at: offset)
    }

    // MARK: - Checking

    /// Throws the same errno a real WASI host reports for a bad pointer, so
    /// the guest can handle it instead of the module being torn down.
    private func checkBounds(offset: UInt32, count: Int) throws {
        let end = Int(offset) + count
        guard count >= 0, end <= byteCount else {
            throw WASIHost.Errno.fault
        }
    }
}

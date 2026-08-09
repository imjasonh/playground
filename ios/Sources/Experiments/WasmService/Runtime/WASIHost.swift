import Foundation
import WasmKit

/// The slice of `wasi_snapshot_preview1` a Go reactor module imports, and
/// deliberately nothing else.
///
/// WasmKit ships a WASI implementation, but it is the wrong shape here twice
/// over. Its `poll_oneoff` returns `ENOTSUP`, and Go's runtime turns any
/// `poll_oneoff` failure into a fatal `throw` the first time its scheduler
/// sleeps — so a Go guest dies on that alone. And it wires the guest to the
/// real filesystem, which is the opposite of what running a stranger's
/// compiled code on a phone should default to.
///
/// So: a clock, randomness, argv/env, a log, and no way to reach anything
/// else. Every filesystem call answers `ENOTCAPABLE`, which is the same thing
/// the guest would see from a runtime started with no preopened directories —
/// a case Go already handles, because it is how `wasmtime` behaves without
/// `--dir`.
final class WASIHost {
    struct Configuration {
        /// `argv[0]` is all Go looks at, but a module is free to read more.
        var arguments: [String] = ["service.wasm"]
        var environment: [String: String] = [:]

        /// How long a single `poll_oneoff` sleep may actually block. Go asks
        /// for sleeps of its own choosing and we are on the thread serving a
        /// request, so an unbounded wait would be a hang. Returning early from
        /// a sleep is allowed — it is a delay, not a deadline.
        var maximumSleep: TimeInterval = 1
    }

    /// Raised by `proc_exit`. Nothing catches it inside the guest, so it
    /// unwinds the whole call and the host learns the module is finished.
    struct GuestExited: Error, LocalizedError {
        let code: UInt32

        var errorDescription: String? {
            code == 0 ? "The module exited" : "The module exited with status \(code)"
        }
    }

    enum HostError: Error, LocalizedError {
        case noMemory

        var errorDescription: String? {
            switch self {
            case .noMemory:
                return "The module exports no memory, so WASI has nowhere to read or write"
            }
        }
    }

    /// WASI's errno numbering. Only the ones this host can produce.
    enum Errno: UInt32, Error {
        case success = 0
        case badFileDescriptor = 8
        case fault = 21
        case invalidArgument = 28
        case notSupported = 58
        case notCapable = 76
    }

    private enum Filetype: UInt8 {
        case characterDevice = 2
    }

    private let configuration: Configuration
    /// Where the guest's stdout and stderr go. Called with whole lines.
    private let log: (String) -> Void
    private let startedAt = DispatchTime.now()
    private var pendingOutput: [UInt32: String] = [:]

    init(configuration: Configuration = Configuration(), log: @escaping (String) -> Void) {
        self.configuration = configuration
        self.log = log
    }

    /// Everything the guest is allowed to import, ready to instantiate with.
    func imports(store: Store) -> Imports {
        var imports = Imports()
        for (name, function) in functions(store: store) {
            imports.define(module: "wasi_snapshot_preview1", name: name, function)
        }
        return imports
    }

    /// Flushes any stdout/stderr the guest wrote without a trailing newline.
    /// A Go panic's last line often has none, and it is the interesting one.
    func flushOutput() {
        for (_, partial) in pendingOutput where !partial.isEmpty {
            log(partial)
        }
        pendingOutput.removeAll()
    }

    // MARK: - The host module

    private func functions(store: Store) -> [String: Function] {
        var functions: [String: Function] = [:]

        functions["args_sizes_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            let (count, size) = Self.vectorSize(of: self.configuration.arguments)
            try memory.writeUInt32(count, at: arguments[0].i32)
            try memory.writeUInt32(size, at: arguments[1].i32)
            return .success
        }

        functions["args_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            try Self.writeVector(
                self.configuration.arguments,
                pointers: arguments[0].i32, buffer: arguments[1].i32, to: memory
            )
            return .success
        }

        functions["environ_sizes_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            let (count, size) = Self.vectorSize(of: self.environmentStrings)
            try memory.writeUInt32(count, at: arguments[0].i32)
            try memory.writeUInt32(size, at: arguments[1].i32)
            return .success
        }

        functions["environ_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            try Self.writeVector(
                self.environmentStrings,
                pointers: arguments[0].i32, buffer: arguments[1].i32, to: memory
            )
            return .success
        }

        functions["clock_time_get"] = errnoFunction(store, [.i32, .i64, .i32]) { memory, arguments in
            guard let nanoseconds = self.clock(arguments[0].i32) else { return .invalidArgument }
            try memory.writeUInt64(nanoseconds, at: arguments[2].i32)
            return .success
        }

        functions["random_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            let count = Int(arguments[1].i32)
            var bytes = [UInt8](repeating: 0, count: count)
            for index in 0..<count {
                bytes[index] = UInt8.random(in: .min ... .max)
            }
            try memory.write(bytes, at: arguments[0].i32)
            return .success
        }

        functions["sched_yield"] = errnoFunction(store, []) { _, _ in .success }

        functions["fd_write"] = errnoFunction(store, [.i32, .i32, .i32, .i32]) { memory, arguments in
            let descriptor = arguments[0].i32
            guard descriptor == 1 || descriptor == 2 else { return .badFileDescriptor }
            let written = try self.collect(
                iovectors: arguments[1].i32, count: arguments[2].i32, from: memory, to: descriptor
            )
            try memory.writeUInt32(written, at: arguments[3].i32)
            return .success
        }

        // stdin is always at end of file. Go reads it only if the module does.
        functions["fd_read"] = errnoFunction(store, [.i32, .i32, .i32, .i32]) { memory, arguments in
            guard arguments[0].i32 == 0 else { return .badFileDescriptor }
            try memory.writeUInt32(0, at: arguments[3].i32)
            return .success
        }

        functions["fd_fdstat_get"] = errnoFunction(store, [.i32, .i32]) { memory, arguments in
            guard arguments[0].i32 <= 2 else { return .badFileDescriptor }
            try Self.writeStdioFdstat(at: arguments[1].i32, to: memory)
            return .success
        }

        functions["fd_fdstat_set_flags"] = errnoFunction(store, [.i32, .i32]) { _, arguments in
            arguments[0].i32 <= 2 ? .success : .badFileDescriptor
        }

        functions["fd_close"] = errnoFunction(store, [.i32]) { _, arguments in
            arguments[0].i32 <= 2 ? .success : .badFileDescriptor
        }

        // No preopens. Go walks upward from fd 3 until this says EBADF, which
        // is how it concludes it has no filesystem — the same answer wasmtime
        // gives when it is started without --dir.
        functions["fd_prestat_get"] = errnoFunction(store, [.i32, .i32]) { _, _ in .badFileDescriptor }
        functions["fd_prestat_dir_name"] = errnoFunction(store, [.i32, .i32, .i32]) { _, _ in .badFileDescriptor }
        functions["path_open"] = errnoFunction(
            store, [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32]
        ) { _, _ in .notCapable }
        functions["path_filestat_get"] = errnoFunction(store, [.i32, .i32, .i32, .i32, .i32]) { _, _ in .notCapable }

        functions["poll_oneoff"] = errnoFunction(store, [.i32, .i32, .i32, .i32]) { memory, arguments in
            try self.poll(
                subscriptions: arguments[0].i32,
                events: arguments[1].i32,
                count: arguments[2].i32,
                produced: arguments[3].i32,
                memory: memory
            )
        }

        functions["proc_exit"] = Function(store: store, parameters: [.i32], results: []) { _, arguments in
            throw GuestExited(code: arguments[0].i32)
        }

        return functions
    }

    // MARK: - poll_oneoff

    /// Go's scheduler sleeps through `poll_oneoff` with a single clock
    /// subscription, so that is the case worth implementing properly. There
    /// are no open descriptors to wait on, so an fd subscription can only be a
    /// guest bug; report it as one per-event rather than failing the whole call.
    private func poll(
        subscriptions: UInt32,
        events: UInt32,
        count: UInt32,
        produced: UInt32,
        memory: GuestMemoryView
    ) throws -> Errno {
        guard count > 0 else { return .invalidArgument }

        var longestSleep: TimeInterval = 0
        var written: UInt32 = 0

        for index in 0..<count {
            let subscription = subscriptions + index * UInt32(Self.subscriptionSize)
            let userdata = try memory.readUInt64(at: subscription)
            let tag = try memory.read(offset: subscription + 8, count: 1)[0]

            var error = Errno.success
            if tag == 0 {
                let flags = try memory.readUInt16(at: subscription + 40)
                let timeout = try memory.readUInt64(at: subscription + 24)
                // Bit 0 is "abstime": the timeout is a clock reading, not a
                // duration. Nothing here waits on wall-clock deadlines, so
                // treat it as "already due" rather than sleeping until 2026.
                if flags & 1 == 0 {
                    longestSleep = max(longestSleep, TimeInterval(timeout) / 1_000_000_000)
                }
            } else {
                error = .badFileDescriptor
            }

            let event = events + written * UInt32(Self.eventSize)
            try memory.writeUInt64(userdata, at: event)
            try memory.writeUInt16(UInt16(error.rawValue), at: event + 8)
            try memory.write([tag], at: event + 10)
            try memory.writeUInt64(0, at: event + 16)
            try memory.writeUInt16(0, at: event + 24)
            written += 1
        }

        if longestSleep > 0 {
            Thread.sleep(forTimeInterval: min(longestSleep, configuration.maximumSleep))
        }
        try memory.writeUInt32(written, at: produced)
        return .success
    }

    private static let subscriptionSize = 48
    private static let eventSize = 32

    // MARK: - Pieces

    private var environmentStrings: [String] {
        configuration.environment
            .sorted { $0.key < $1.key }
            .map { "\($0.key)=\($0.value)" }
    }

    private func clock(_ identifier: UInt32) -> UInt64? {
        switch identifier {
        case 0:  // realtime
            return UInt64(Date().timeIntervalSince1970 * 1_000_000_000)
        case 1, 2, 3:  // monotonic, process cpu, thread cpu
            return DispatchTime.now().uptimeNanoseconds - startedAt.uptimeNanoseconds
        default:
            return nil
        }
    }

    /// Gathers an iovec array into whole lines of log output. Buffering by
    /// descriptor matters because Go writes a panic in several `fd_write`
    /// calls that only make sense reassembled.
    private func collect(
        iovectors: UInt32,
        count: UInt32,
        from memory: GuestMemoryView,
        to descriptor: UInt32
    ) throws -> UInt32 {
        var written: UInt32 = 0
        var text = pendingOutput[descriptor] ?? ""

        for index in 0..<count {
            let entry = iovectors + index * 8
            let offset = try memory.readUInt32(at: entry)
            let length = try memory.readUInt32(at: entry + 4)
            guard length > 0 else { continue }
            let bytes = try memory.read(offset: offset, count: Int(length))
            text += String(decoding: bytes, as: UTF8.self)
            written += length
        }

        while let newline = text.firstIndex(of: "\n") {
            log(String(text[text.startIndex..<newline]))
            text = String(text[text.index(after: newline)...])
        }
        pendingOutput[descriptor] = text
        return written
    }

    private static func vectorSize(of strings: [String]) -> (count: UInt32, bytes: UInt32) {
        let bytes = strings.reduce(0) { $0 + $1.utf8.count + 1 }
        return (UInt32(strings.count), UInt32(bytes))
    }

    /// The WASI layout for argv and environ: an array of pointers, then the
    /// NUL-terminated strings they point into.
    private static func writeVector(
        _ strings: [String],
        pointers: UInt32,
        buffer: UInt32,
        to memory: GuestMemoryView
    ) throws {
        var cursor = buffer
        for (index, string) in strings.enumerated() {
            try memory.writeUInt32(cursor, at: pointers + UInt32(index) * 4)
            let bytes = Array(string.utf8) + [0]
            try memory.write(bytes, at: cursor)
            cursor += UInt32(bytes.count)
        }
    }

    /// `fdstat` is 24 bytes: filetype, two pad, flags, four pad, then two
    /// rights bitmaps. Claiming every right is right here — the descriptor is
    /// a character device the host fully controls.
    private static func writeStdioFdstat(at offset: UInt32, to memory: GuestMemoryView) throws {
        try memory.write([UInt8](repeating: 0, count: 24), at: offset)
        try memory.write([Filetype.characterDevice.rawValue], at: offset)
        try memory.writeUInt64(.max, at: offset + 8)
        try memory.writeUInt64(.max, at: offset + 16)
    }

    // MARK: - Wiring

    /// Wraps a body that returns an errno, so an out-of-bounds guest pointer
    /// becomes `EFAULT` for the guest instead of a trap that kills the module.
    private func errnoFunction(
        _ store: Store,
        _ parameters: [ValueType],
        _ body: @escaping (GuestMemoryView, [Value]) throws -> Errno
    ) -> Function {
        Function(store: store, parameters: parameters, results: [.i32]) { caller, arguments in
            guard let memory = caller.instance?.exports[memory: "memory"] else {
                throw HostError.noMemory
            }
            do {
                return [.i32(try body(GuestMemoryView(memory: memory), arguments).rawValue)]
            } catch let errno as Errno {
                return [.i32(errno.rawValue)]
            }
        }
    }
}

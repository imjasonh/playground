import WAT
import XCTest

@testable import Playground

/// Covers the wasm side of Wasm Service: the host ABI, and the WASI calls the
/// host implements.
///
/// Every module here is assembled from WebAssembly text at test time, so the
/// suite proves the host works without a multi-megabyte fixture in git and
/// without a Go toolchain. `WasmServiceGoModuleTests` runs the real thing when
/// CI has built it.
///
/// The trick that makes WASI testable through the same door: a module reports
/// the result of the WASI call it made *as its HTTP response*, by leaving the
/// bytes in memory and returning that region. So `guest.handle(…)` hands the
/// test whatever the module saw.
final class WasmServiceGuestTests: XCTestCase {
    // MARK: - The handler ABI

    func testGuestServesACannedResponse() throws {
        let response = "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"
        let bytes = Array(response.utf8)
        let guest = try makeGuest(
            """
            (module
              (memory (export "memory") 1)
              (data (i32.const 0) "\(watEscaped(bytes))")
              (func (export "_initialize"))
              (func (export "http_abi_version") (result i32) (i32.const 1))
              (func (export "http_alloc") (param i32) (result i32) (i32.const 4096))
              (func (export "http_handle") (param i32 i32) (result i64)
                (i64.const \(bytes.count))))
            """
        )

        let served = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        XCTAssertEqual(String(decoding: served, as: UTF8.self), response)
    }

    /// The module hands back exactly the region it was given, so a correct
    /// round trip means the host allocated, wrote, and re-read the same bytes.
    func testHostWritesTheRequestWhereTheGuestAskedFor() throws {
        let guest = try makeGuest(echoModule)
        let request = "POST /echo HTTP/1.1\r\nHost: phone\r\nContent-Length: 4\r\n\r\nbody"

        let served = try guest.handle(Data(request.utf8))
        XCTAssertEqual(String(decoding: served, as: UTF8.self), request)
    }

    func testLargeRequestSurvivesTheRoundTrip() throws {
        let guest = try makeGuest(echoModule)
        let request = "POST / HTTP/1.1\r\n\r\n" + String(repeating: "x", count: 40_000)

        let served = try guest.handle(Data(request.utf8))
        XCTAssertEqual(served.count, request.utf8.count)
    }

    // MARK: - Refusing modules the host cannot drive

    func testModuleWithoutInitializeIsRejected() throws {
        XCTAssertThrowsError(
            try makeGuest(
                """
                (module
                  (memory (export "memory") 1)
                  (func (export "http_abi_version") (result i32) (i32.const 1))
                  (func (export "http_alloc") (param i32) (result i32) (i32.const 4096))
                  (func (export "http_handle") (param i32 i32) (result i64) (i64.const 0)))
                """
            )
        ) { error in
            XCTAssertEqual(error as? WasmHTTPGuest.GuestError, .notAReactor)
        }
    }

    func testModuleWithAnUnknownABIIsRejected() throws {
        XCTAssertThrowsError(
            try makeGuest(
                """
                (module
                  (memory (export "memory") 1)
                  (func (export "_initialize"))
                  (func (export "http_abi_version") (result i32) (i32.const 99))
                  (func (export "http_alloc") (param i32) (result i32) (i32.const 4096))
                  (func (export "http_handle") (param i32 i32) (result i64) (i64.const 0)))
                """
            )
        ) { error in
            XCTAssertEqual(error as? WasmHTTPGuest.GuestError, .unsupportedABI(found: 99))
        }
    }

    func testModuleThatRefusesToAllocateIsReported() throws {
        let guest = try makeGuest(
            """
            (module
              (memory (export "memory") 1)
              (func (export "_initialize"))
              (func (export "http_abi_version") (result i32) (i32.const 1))
              (func (export "http_alloc") (param i32) (result i32) (i32.const 0))
              (func (export "http_handle") (param i32 i32) (result i64) (i64.const 0)))
            """
        )

        XCTAssertThrowsError(try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))) { error in
            XCTAssertEqual(error as? WasmHTTPGuest.GuestError, .allocationRefused)
        }
    }

    // MARK: - WASI

    /// A monotonic clock has to advance and has to be reported without error;
    /// Go's runtime reads it constantly.
    func testMonotonicClockAdvances() throws {
        let guest = try makeGuest(wasiProbe(
            import: #"(import "wasi_snapshot_preview1" "clock_time_get" (func $call (param i32 i64 i32) (result i32)))"#,
            body: "(i32.store (i32.const 0) (call $call (i32.const 1) (i64.const 0) (i32.const 8)))",
            responseLength: 16
        ))

        let first = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        Thread.sleep(forTimeInterval: 0.02)
        let second = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))

        XCTAssertEqual(readUInt32(first, at: 0), 0, "clock_time_get reported an errno")
        XCTAssertGreaterThan(readUInt64(second, at: 8), readUInt64(first, at: 8))
    }

    func testWallClockIsPlausible() throws {
        let guest = try makeGuest(wasiProbe(
            import: #"(import "wasi_snapshot_preview1" "clock_time_get" (func $call (param i32 i64 i32) (result i32)))"#,
            body: "(i32.store (i32.const 0) (call $call (i32.const 0) (i64.const 0) (i32.const 8)))",
            responseLength: 16
        ))

        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        let seconds = Double(readUInt64(seen, at: 8)) / 1_000_000_000
        XCTAssertEqual(seconds, Date().timeIntervalSince1970, accuracy: 60)
    }

    func testRandomGetFillsTheBuffer() throws {
        let guest = try makeGuest(wasiProbe(
            import: #"(import "wasi_snapshot_preview1" "random_get" (func $call (param i32 i32) (result i32)))"#,
            body: "(i32.store (i32.const 0) (call $call (i32.const 8) (i32.const 32)))",
            responseLength: 40
        ))

        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        XCTAssertEqual(readUInt32(seen, at: 0), 0)
        XCTAssertGreaterThan(Set(seen.dropFirst(8)).count, 1, "random_get left the buffer untouched")
    }

    /// Go writes a panic in several `fd_write` calls; the host has to
    /// reassemble them into lines rather than logging fragments.
    func testStdoutIsCollectedIntoLines() throws {
        var lines: [String] = []
        let message = Array("first line\nsecond".utf8)
        let guest = try makeGuest(
            """
            (module
              (import "wasi_snapshot_preview1" "fd_write"
                (func $write (param i32 i32 i32 i32) (result i32)))
              (memory (export "memory") 1)
              (data (i32.const 64) "\(watEscaped(message))")
              (func (export "_initialize"))
              (func (export "http_abi_version") (result i32) (i32.const 1))
              (func (export "http_alloc") (param i32) (result i32) (i32.const 8192))
              (func (export "http_handle") (param i32 i32) (result i64)
                ;; one iovec at 16: {base = 64, length}
                (i32.store (i32.const 16) (i32.const 64))
                (i32.store (i32.const 20) (i32.const \(message.count)))
                (i32.store (i32.const 0) (call $write (i32.const 1) (i32.const 16) (i32.const 1) (i32.const 4)))
                (i64.const 8)))
            """,
            log: { lines.append($0) }
        )

        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        XCTAssertEqual(readUInt32(seen, at: 0), 0, "fd_write reported an errno")
        XCTAssertEqual(readUInt32(seen, at: 4), UInt32(message.count), "fd_write miscounted")
        XCTAssertEqual(lines, ["first line"], "a partial line should be held back")

        guest.flushLog()
        XCTAssertEqual(lines, ["first line", "second"], "flush should release the tail")
    }

    /// The one WasmKit's own WASI gets wrong for a Go guest: it answers
    /// ENOTSUP, and Go turns any poll_oneoff error into a fatal throw.
    func testPollOneoffSleepsAndReportsAnEvent() throws {
        let guest = try makeGuest(
            """
            (module
              (import "wasi_snapshot_preview1" "poll_oneoff"
                (func $poll (param i32 i32 i32 i32) (result i32)))
              (memory (export "memory") 1)
              (func (export "_initialize"))
              (func (export "http_abi_version") (result i32) (i32.const 1))
              (func (export "http_alloc") (param i32) (result i32) (i32.const 8192))
              (func (export "http_handle") (param i32 i32) (result i64)
                ;; one clock subscription at 256: userdata 7, tag 0, 10ms relative
                (i64.store (i32.const 256) (i64.const 7))
                (i32.store8 (i32.const 264) (i32.const 0))
                (i32.store (i32.const 272) (i32.const 1))
                (i64.store (i32.const 280) (i64.const 10000000))
                (i32.store16 (i32.const 296) (i32.const 0))
                ;; events at 512, count written to 4
                (i32.store (i32.const 0) (call $poll (i32.const 256) (i32.const 512) (i32.const 1) (i32.const 4)))
                ;; report: errno, event count, then the event's userdata and error
                (i64.store (i32.const 8) (i64.load (i32.const 512)))
                (i32.store16 (i32.const 16) (i32.load16_u (i32.const 520)))
                (i64.const 24)))
            """
        )

        let started = Date()
        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))

        XCTAssertEqual(readUInt32(seen, at: 0), 0, "poll_oneoff reported an errno")
        XCTAssertEqual(readUInt32(seen, at: 4), 1, "poll_oneoff produced no events")
        XCTAssertEqual(readUInt64(seen, at: 8), 7, "the event lost its userdata")
        XCTAssertEqual(readUInt32(seen, at: 16) & 0xffff, 0, "the event reported an error")
        XCTAssertGreaterThanOrEqual(Date().timeIntervalSince(started), 0.005, "poll_oneoff did not sleep")
    }

    /// No preopens, so Go concludes it has no filesystem — the same answer
    /// wasmtime gives without `--dir`.
    func testFilesystemIsClosed() throws {
        let guest = try makeGuest(wasiProbe(
            import: #"(import "wasi_snapshot_preview1" "fd_prestat_get" (func $call (param i32 i32) (result i32)))"#,
            body: "(i32.store (i32.const 0) (call $call (i32.const 3) (i32.const 8)))",
            responseLength: 16
        ))

        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        XCTAssertEqual(readUInt32(seen, at: 0), WASIHost.Errno.badFileDescriptor.rawValue)
    }

    /// A guest pointer past the end of memory must come back as EFAULT rather
    /// than reading whatever the app has at that address.
    func testOutOfBoundsPointerBecomesEFAULT() throws {
        let guest = try makeGuest(wasiProbe(
            // One page is 65536 bytes; ask it to write the timestamp far past that.
            import: #"(import "wasi_snapshot_preview1" "clock_time_get" (func $call (param i32 i64 i32) (result i32)))"#,
            body: "(i32.store (i32.const 0) (call $call (i32.const 1) (i64.const 0) (i32.const 65534)))",
            responseLength: 8
        ))

        let seen = try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8))
        XCTAssertEqual(readUInt32(seen, at: 0), WASIHost.Errno.fault.rawValue)
    }

    func testProcExitStopsTheModule() throws {
        let guest = try makeGuest(
            """
            (module
              (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
              (memory (export "memory") 1)
              (func (export "_initialize"))
              (func (export "http_abi_version") (result i32) (i32.const 1))
              (func (export "http_alloc") (param i32) (result i32) (i32.const 4096))
              (func (export "http_handle") (param i32 i32) (result i64)
                (call $exit (i32.const 3))
                (i64.const 0)))
            """
        )

        // Only that it unwinds is asserted: WasmKit may or may not wrap a host
        // function's error on the way out, and the runtime handles both — a
        // recognized `GuestExited` becomes a 503, anything else a 500.
        XCTAssertThrowsError(try guest.handle(Data("GET / HTTP/1.1\r\n\r\n".utf8)))
    }

    // MARK: - Helpers

    /// Returns exactly the region it was handed, so the response *is* the
    /// request if the host got the plumbing right.
    private let echoModule = """
        (module
          (memory (export "memory") 2)
          (func (export "_initialize"))
          (func (export "http_abi_version") (result i32) (i32.const 1))
          (func (export "http_alloc") (param i32) (result i32) (i32.const 4096))
          (func (export "http_handle") (param i32 i32) (result i64)
            (i64.or
              (i64.shl (i64.extend_i32_u (local.get 0)) (i64.const 32))
              (i64.extend_i32_u (local.get 1)))))
        """

    /// A module whose whole job is to make one WASI call and report what
    /// happened as its response body.
    private func wasiProbe(import declaration: String, body: String, responseLength: Int) -> String {
        """
        (module
          \(declaration)
          (memory (export "memory") 1)
          (func (export "_initialize"))
          (func (export "http_abi_version") (result i32) (i32.const 1))
          (func (export "http_alloc") (param i32) (result i32) (i32.const 8192))
          (func (export "http_handle") (param i32 i32) (result i64)
            \(body)
            (i64.const \(responseLength))))
        """
    }

    private func makeGuest(
        _ text: String,
        log: @escaping (String) -> Void = { _ in }
    ) throws -> WasmHTTPGuest {
        let bytes = try wat2wasm(text)
        return try WasmHTTPGuest(
            module: Data(bytes),
            wasi: WASIHost(configuration: WASIHost.Configuration(), log: log),
            memoryLimit: 16 << 20
        )
    }

    private func watEscaped(_ bytes: [UInt8]) -> String {
        bytes.map { String(format: "\\%02x", $0) }.joined()
    }

    private func readUInt32(_ data: Data, at offset: Int) -> UInt32 {
        let bytes = [UInt8](data)
        guard bytes.count >= offset + 4 else { return .max }
        return (0..<4).reversed().reduce(UInt32(0)) { $0 << 8 | UInt32(bytes[offset + $1]) }
    }

    private func readUInt64(_ data: Data, at offset: Int) -> UInt64 {
        let bytes = [UInt8](data)
        guard bytes.count >= offset + 8 else { return .max }
        return (0..<8).reversed().reduce(UInt64(0)) { $0 << 8 | UInt64(bytes[offset + $1]) }
    }
}

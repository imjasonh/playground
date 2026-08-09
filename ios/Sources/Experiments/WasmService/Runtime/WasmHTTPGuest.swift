import Foundation

// `Store.resourceLimiter` is the only public way to cap how far a module may
// grow its linear memory, and WasmKit 0.2.2 still marks it `@_spi(Fuzzing)`
// ("consider making this public", says the source). The package is pinned to an
// exact version, so importing the SPI is a known quantity rather than a bet on
// an unstable interface — and the alternative is no cap at all. See MemoryCap.
@_spi(Fuzzing) import WasmKit

/// One instantiated WebAssembly module, driven through the HTTP handler ABI
/// that `wasm-hello` documents: `http_alloc` for a buffer, `http_handle` for
/// the exchange, raw HTTP/1.1 bytes in both directions.
///
/// WasmKit interprets rather than compiles, which is the whole reason this can
/// exist inside an App Store app: iOS grants no JIT entitlement, so any wasm
/// running outside a `WKWebView` has to be interpreted. The cost is speed, and
/// the benefit is that the module is ordinary app code — it keeps running when
/// a webview would have been suspended, and it can be handed a real socket.
///
/// Not thread-safe by design. A wasm instance has one linear memory and one
/// notion of "the buffer I just handed out", so callers serialize; the server
/// owns a queue for exactly this.
final class WasmHTTPGuest {
    /// The ABI revision this host knows how to speak.
    static let supportedABIVersion: UInt32 = 1

    enum GuestError: Error, LocalizedError, Equatable {
        case notAReactor
        case missingExport(String)
        case unsupportedABI(found: UInt32)
        case allocationRefused
        case malformedResult(String)

        var errorDescription: String? {
            switch self {
            case .notAReactor:
                return "This module has no _initialize, so it is a program rather than a service. "
                    + "Build it with -buildmode=c-shared (Go) or as a reactor."
            case .missingExport(let name):
                return "The module does not export \(name), so it does not implement the HTTP handler ABI"
            case .unsupportedABI(let found):
                return "The module speaks HTTP ABI version \(found); "
                    + "this app speaks \(WasmHTTPGuest.supportedABIVersion)"
            case .allocationRefused:
                return "The module refused to allocate a request buffer"
            case .malformedResult(let detail):
                return "The module returned something unusable: \(detail)"
            }
        }
    }

    /// What the UI shows about a module once it is loaded.
    struct Summary {
        var memoryBytes: Int
        var abiVersion: UInt32
        var exportedFunctions: [String]
    }

    private let store: Store
    private let instance: Instance
    private let memory: Memory
    private let allocate: Function
    private let handleRequest: Function
    private let wasi: WASIHost

    private(set) var summary: Summary

    /// Parses, validates, instantiates, and starts the module's runtime. All
    /// of that is slow enough on a phone (seconds, for a Go module) that it
    /// belongs off the main thread.
    init(module bytes: Data, wasi: WASIHost, memoryLimit: Int) throws {
        self.wasi = wasi

        let store = Store(engine: Engine())
        store.resourceLimiter = MemoryCap(limit: memoryLimit)
        self.store = store

        let module = try parseWasm(bytes: [UInt8](bytes))
        let instance = try module.instantiate(store: store, imports: wasi.imports(store: store))
        self.instance = instance

        guard let memory = instance.exports[memory: "memory"] else {
            throw GuestError.missingExport("memory")
        }
        self.memory = memory

        // A reactor's runtime starts here rather than at instantiation, which
        // is what makes the instance reusable across requests.
        guard let initialize = instance.exports[function: "_initialize"] else {
            throw GuestError.notAReactor
        }
        _ = try initialize()

        guard let version = instance.exports[function: "http_abi_version"] else {
            throw GuestError.missingExport("http_abi_version")
        }
        guard case .i32(let reported)? = try version().first else {
            throw GuestError.malformedResult("http_abi_version did not return an i32")
        }
        guard reported == Self.supportedABIVersion else {
            throw GuestError.unsupportedABI(found: reported)
        }

        guard let allocate = instance.exports[function: "http_alloc"] else {
            throw GuestError.missingExport("http_alloc")
        }
        guard let handleRequest = instance.exports[function: "http_handle"] else {
            throw GuestError.missingExport("http_handle")
        }
        self.allocate = allocate
        self.handleRequest = handleRequest

        self.summary = Summary(
            memoryBytes: memory.data.count,
            abiVersion: reported,
            exportedFunctions: instance.exports.map { $0.name }.sorted()
        )
    }

    /// Serves one exchange: raw request bytes in, raw response bytes out.
    func handle(_ request: Data) throws -> Data {
        let length = UInt32(request.count)

        guard case .i32(let offset)? = try allocate([.i32(length)]).first else {
            throw GuestError.malformedResult("http_alloc did not return an i32")
        }
        guard offset != 0 else { throw GuestError.allocationRefused }

        let view = GuestMemoryView(memory: memory)
        try view.write(request, at: offset)

        guard case .i64(let packed)? = try handleRequest([.i32(offset), .i32(length)]).first else {
            throw GuestError.malformedResult("http_handle did not return an i64")
        }
        // offset in the high half, length in the low half.
        let responseOffset = UInt32(truncatingIfNeeded: packed >> 32)
        let responseLength = UInt32(truncatingIfNeeded: packed)
        guard packed != 0, responseLength > 0 else {
            throw GuestError.malformedResult("http_handle produced no response")
        }

        summary.memoryBytes = memory.data.count
        return try view.readData(offset: responseOffset, count: Int(responseLength))
    }

    /// Emits whatever the guest wrote to stdout or stderr without a newline —
    /// the tail of a Go panic lives there.
    func flushLog() {
        wasi.flushOutput()
    }
}

/// Refuses memory growth past a ceiling.
///
/// A wasm module can ask for as much linear memory as it likes, and iOS
/// answers an app that takes too much by killing it outright, with no error to
/// report and nothing in the log. Bounding growth turns "the app disappeared"
/// into a trap the guest sees and the UI can explain.
private struct MemoryCap: ResourceLimiter {
    let limit: Int

    func limitMemoryGrowth(to desired: Int) throws -> Bool { desired <= limit }
    func limitTableGrowth(to desired: Int) throws -> Bool { true }
}

import Foundation

/// Owns the running service: one instantiated module, one listening socket,
/// and the single queue both live on.
///
/// Everything that touches the wasm instance — parsing it, starting its
/// runtime, serving a request — happens on `queue`, because a module has one
/// linear memory and one outstanding buffer and cannot be entered twice at
/// once. Keeping that rule in one small class is why the model above it can be
/// ordinary `@MainActor` UI code.
final class WasmServiceRuntime {
    struct Configuration {
        var port: UInt16 = 8080
        var loopbackOnly = false
        /// Enough for a Go runtime and a request in flight, low enough that
        /// iOS is not tempted to kill the app instead.
        var memoryLimit = 256 << 20
        var environment: [String: String] = [:]
    }

    struct Started {
        var port: UInt16
        var summary: WasmHTTPGuest.Summary
    }

    /// Guest stdout/stderr and host-side notes, a line at a time. Called from
    /// the guest queue; the model hops to the main actor.
    var onLog: ((String) -> Void)?
    /// The running total of requests served.
    var onRequestServed: ((Int) -> Void)?

    private let queue = DispatchQueue(label: "io.github.imjasonh.playground.wasmservice.guest")
    private var guest: WasmHTTPGuest?
    private var server: WasmHTTPServer?
    private var served = 0

    var isRunning: Bool { server != nil }

    func start(module: Data, configuration: Configuration = Configuration()) async throws -> Started {
        let summary = try await instantiate(module: module, configuration: configuration)

        let server = WasmHTTPServer(
            configuration: WasmHTTPServer.Configuration(
                port: configuration.port,
                loopbackOnly: configuration.loopbackOnly
            ),
            guestQueue: queue,
            exchange: { [weak self] request in
                self?.exchange(request) ?? HTTPRequestFramer.refusal(
                    status: 503, reason: "the service is shutting down"
                )
            }
        )
        let port = try await server.start()
        self.server = server
        return Started(port: port, summary: summary)
    }

    func stop() {
        server?.stop()
        server = nil
        queue.sync {
            guest?.flushLog()
            guest = nil
        }
        served = 0
    }

    // MARK: - Guest

    /// Parsing, validating, and translating a 5 MB module, then starting a Go
    /// runtime under an interpreter, takes seconds on a phone. It runs on the
    /// guest queue both because it has to and so the UI keeps painting.
    private func instantiate(
        module: Data,
        configuration: Configuration
    ) async throws -> WasmHTTPGuest.Summary {
        try await withCheckedThrowingContinuation { continuation in
            queue.async { [weak self] in
                guard let self else {
                    continuation.resume(throwing: CancellationError())
                    return
                }
                do {
                    let wasi = WASIHost(
                        configuration: WASIHost.Configuration(
                            arguments: ["service.wasm"],
                            environment: configuration.environment
                        ),
                        log: { [weak self] line in self?.onLog?(line) }
                    )
                    let guest = try WasmHTTPGuest(
                        module: module, wasi: wasi, memoryLimit: configuration.memoryLimit
                    )
                    self.guest = guest
                    continuation.resume(returning: guest.summary)
                } catch {
                    continuation.resume(throwing: error)
                }
            }
        }
    }

    /// Runs on the guest queue, one request at a time.
    private func exchange(_ request: Data) -> Data {
        guard let guest else {
            return HTTPRequestFramer.refusal(status: 503, reason: "no module is loaded")
        }
        do {
            let response = try guest.handle(request)
            served += 1
            onRequestServed?(served)
            return response
        } catch let exit as WASIHost.GuestExited {
            // A module that called proc_exit is finished; there is no way to
            // re-enter it, so drop it rather than trap on every later request.
            guest.flushLog()
            self.guest = nil
            onLog?(exit.localizedDescription)
            return HTTPRequestFramer.refusal(status: 503, reason: exit.localizedDescription)
        } catch {
            guest.flushLog()
            onLog?("request failed: \(error.localizedDescription)")
            return HTTPRequestFramer.refusal(status: 500, reason: error.localizedDescription)
        }
    }
}

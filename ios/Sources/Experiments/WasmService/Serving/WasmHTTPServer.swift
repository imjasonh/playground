import Foundation
import Network

/// A real TCP server that hands each request to a wasm module and writes back
/// whatever bytes the module produced.
///
/// This is the half of the service that the guest cannot be: `wasi_snapshot_
/// preview1` has no sockets, so the module can never `accept()`. Splitting it
/// this way is not a workaround, though — it is what lets the guest be a plain
/// request handler, and therefore what lets a non-JIT interpreter run it.
///
/// Unlike Container Lab's loopback server, this one binds every interface by
/// default, so the phone is reachable from a laptop on the same Wi-Fi (and,
/// later, over a tailnet). It answers any method, reads request bodies, and
/// adds nothing to the response: the guest's bytes go out untouched.
final class WasmHTTPServer {
    /// Runs one exchange. Called on the server's guest queue, one at a time.
    typealias Exchange = (Data) -> Data

    struct Configuration {
        /// 0 asks the system for a free port.
        var port: UInt16 = 8080
        /// Bind loopback only, so nothing off-device can reach the module.
        var loopbackOnly: Bool = false
        var maximumBodyBytes: Int = 8 << 20
    }

    private let configuration: Configuration
    private let exchange: Exchange
    private let queue = DispatchQueue(label: "io.github.imjasonh.playground.wasmservice.listener")
    /// The queue every `exchange` runs on. Injected rather than created here
    /// because the module was instantiated on it too: a wasm instance has one
    /// linear memory and one outstanding buffer, so everything that touches it
    /// — instantiation included — has to be the same serial queue.
    private let guestQueue: DispatchQueue

    private var listener: NWListener?
    private(set) var port: UInt16?

    /// Resumes the start continuation exactly once, however the listener's
    /// state churns afterwards.
    private final class StartupGate: @unchecked Sendable {
        private let lock = NSLock()
        private var resumed = false

        func resumeOnce(_ body: () -> Void) {
            lock.lock()
            let alreadyResumed = resumed
            resumed = true
            lock.unlock()
            if !alreadyResumed { body() }
        }
    }

    init(
        configuration: Configuration = Configuration(),
        guestQueue: DispatchQueue,
        exchange: @escaping Exchange
    ) {
        self.configuration = configuration
        self.guestQueue = guestQueue
        self.exchange = exchange
    }

    deinit {
        listener?.cancel()
    }

    func start() async throws -> UInt16 {
        if let port { return port }

        let parameters = NWParameters.tcp
        parameters.allowLocalEndpointReuse = true
        parameters.includePeerToPeer = false

        let requestedPort = NWEndpoint.Port(rawValue: configuration.port) ?? .any
        if configuration.loopbackOnly {
            // The port has to be repeated here. `requiredLocalEndpoint` pins
            // the whole endpoint, so pairing a loopback host with `.any` would
            // quietly override the port the caller asked for.
            parameters.requiredLocalEndpoint = NWEndpoint.hostPort(
                host: .ipv4(.loopback), port: requestedPort
            )
        }

        let listener = try NWListener(using: parameters, on: requestedPort)
        self.listener = listener

        listener.newConnectionHandler = { [weak self] connection in
            self?.accept(connection)
        }

        let startup = StartupGate()
        let startQueue = queue
        let assignedPort: UInt16 = try await withCheckedThrowingContinuation { continuation in
            listener.stateUpdateHandler = { state in
                startQueue.async {
                    switch state {
                    case .ready:
                        guard let rawPort = listener.port?.rawValue else {
                            startup.resumeOnce { continuation.resume(throwing: WasmHTTPServerError.noPort) }
                            return
                        }
                        startup.resumeOnce { continuation.resume(returning: rawPort) }
                    case .failed(let error):
                        startup.resumeOnce { continuation.resume(throwing: error) }
                    case .cancelled:
                        startup.resumeOnce { continuation.resume(throwing: WasmHTTPServerError.cancelled) }
                    default:
                        break
                    }
                }
            }
            listener.start(queue: queue)
        }

        port = assignedPort
        return assignedPort
    }

    func stop() {
        listener?.cancel()
        listener = nil
        port = nil
    }

    // MARK: - Connections

    private func accept(_ connection: NWConnection) {
        connection.start(queue: queue)
        receive(on: connection, buffer: Data())
    }

    private func receive(on connection: NWConnection, buffer: Data) {
        connection.receive(minimumIncompleteLength: 1, maximumLength: 64 * 1024) { [weak self] chunk, _, isComplete, error in
            guard let self else {
                connection.cancel()
                return
            }
            guard error == nil else {
                connection.cancel()
                return
            }

            var accumulated = buffer
            if let chunk, !chunk.isEmpty {
                accumulated.append(chunk)
            }

            switch HTTPRequestFramer.examine(accumulated, maximumBodyBytes: self.configuration.maximumBodyBytes) {
            case .complete(let byteCount):
                self.serve(accumulated.prefix(byteCount), on: connection)
            case .refuse(let status, let reason):
                self.send(HTTPRequestFramer.refusal(status: status, reason: reason), on: connection)
            case .needMore:
                if isComplete {
                    // The client hung up mid-request; there is nobody to answer.
                    connection.cancel()
                    return
                }
                self.receive(on: connection, buffer: accumulated)
            }
        }
    }

    /// Runs the guest on its own queue so a slow module — and interpreted wasm
    /// is slow — never blocks the listener from accepting the next connection.
    private func serve(_ request: Data, on connection: NWConnection) {
        guestQueue.async { [weak self] in
            guard let self else {
                connection.cancel()
                return
            }
            let response = self.exchange(Data(request))
            self.send(response, on: connection)
        }
    }

    /// One response, then close. Keep-alive would buy little here: the guest
    /// serves one request at a time anyway, so a held-open connection would
    /// only pin a slot.
    private func send(_ response: Data, on connection: NWConnection) {
        connection.send(content: response, isComplete: true, completion: .contentProcessed { _ in
            connection.cancel()
        })
    }
}

enum WasmHTTPServerError: Error, LocalizedError {
    case noPort
    case cancelled

    var errorDescription: String? {
        switch self {
        case .noPort: return "The server started without a port"
        case .cancelled: return "The server was cancelled"
        }
    }
}

import Foundation
import Network

/// A tiny HTTP/1.1 server bound to `127.0.0.1`, used to give the runtime
/// webview a real origin.
///
/// Why this exists at all: `WKWebView` will not treat a custom
/// `WKURLSchemeHandler` scheme as a secure context, and it ignores the
/// service-worker COOP/COEP shims that work in Safari. Without cross-origin
/// isolation there is no `SharedArrayBuffer`, and without that there are no
/// wasm threads — so no emulator. A loopback origin is a potentially
/// trustworthy origin whose response headers we control, which is the one
/// combination that gets us there.
///
/// Only GET and HEAD are answered; there is nothing to POST to.
final class LoopbackServer {
    struct Request {
        var method: String
        var path: String
        var query: [String: String]
        var headers: [String: String]
    }

    struct Response {
        var status: Int
        var headers: [String: String]
        var body: Data

        static func notFound() -> Response {
            Response(status: 404, headers: ["Content-Type": "text/plain; charset=utf-8"], body: Data("not found".utf8))
        }

        static func data(_ body: Data, contentType: String) -> Response {
            Response(status: 200, headers: ["Content-Type": contentType], body: body)
        }

        static func text(_ string: String, contentType: String = "text/plain; charset=utf-8") -> Response {
            Response(status: 200, headers: ["Content-Type": contentType], body: Data(string.utf8))
        }
    }

    typealias Handler = (Request) -> Response

    /// Headers added to every response. `require-corp` means every subresource
    /// must opt in, so same-origin assets get `Cross-Origin-Resource-Policy`.
    static let isolationHeaders: [String: String] = [
        "Cross-Origin-Opener-Policy": "same-origin",
        "Cross-Origin-Embedder-Policy": "require-corp",
        "Cross-Origin-Resource-Policy": "same-origin",
        "Cache-Control": "no-store"
    ]

    private let handler: Handler
    private let queue = DispatchQueue(label: "io.github.imjasonh.playground.containerlab.loopback")
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

    init(handler: @escaping Handler) {
        self.handler = handler
    }

    deinit {
        listener?.cancel()
    }

    var baseURL: URL? {
        guard let port else { return nil }
        return URL(string: "http://127.0.0.1:\(port)/")
    }

    /// Binds an ephemeral loopback port and resolves once the listener is ready.
    func start() async throws -> UInt16 {
        if let port { return port }

        let parameters = NWParameters.tcp
        parameters.allowLocalEndpointReuse = true
        parameters.requiredLocalEndpoint = NWEndpoint.hostPort(
            host: .ipv4(.loopback),
            port: .any
        )

        let listener = try NWListener(using: parameters)
        self.listener = listener

        listener.newConnectionHandler = { [weak self] connection in
            self?.accept(connection)
        }

        // The state handler deliberately captures a small box instead of the
        // server: NWListener calls it on its own queue, and `self` is not
        // Sendable.
        let startup = StartupGate()
        let startQueue = queue
        let assignedPort: UInt16 = try await withCheckedThrowingContinuation { continuation in
            listener.stateUpdateHandler = { state in
                startQueue.async {
                    switch state {
                    case .ready:
                        guard let rawPort = listener.port?.rawValue else {
                            startup.resumeOnce { continuation.resume(throwing: LoopbackServerError.noPort) }
                            return
                        }
                        startup.resumeOnce { continuation.resume(returning: rawPort) }
                    case .failed(let error):
                        startup.resumeOnce { continuation.resume(throwing: error) }
                    case .cancelled:
                        startup.resumeOnce { continuation.resume(throwing: LoopbackServerError.cancelled) }
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

    // MARK: - Connection handling

    private func accept(_ connection: NWConnection) {
        connection.start(queue: queue)
        receiveRequest(on: connection, buffer: Data())
    }

    private func receiveRequest(on connection: NWConnection, buffer: Data) {
        connection.receive(minimumIncompleteLength: 1, maximumLength: 64 * 1024) { [weak self] chunk, _, isComplete, error in
            guard let self else { return }
            var accumulated = buffer
            if let chunk, !chunk.isEmpty {
                accumulated.append(chunk)
            }

            if error != nil {
                connection.cancel()
                return
            }

            if let headerEnd = Self.headerTerminator(in: accumulated) {
                let head = String(decoding: accumulated[..<headerEnd], as: UTF8.self)
                self.respond(to: head, on: connection)
                return
            }

            if isComplete || accumulated.count > 1_000_000 {
                connection.cancel()
                return
            }
            self.receiveRequest(on: connection, buffer: accumulated)
        }
    }

    private func respond(to head: String, on connection: NWConnection) {
        let response: Response
        if let request = Self.parseRequest(head) {
            if request.method == "GET" || request.method == "HEAD" {
                var handled = handler(request)
                if request.method == "HEAD" {
                    handled.headers["Content-Length"] = String(handled.body.count)
                    handled.body = Data()
                }
                response = handled
            } else {
                response = Response(
                    status: 405,
                    headers: ["Content-Type": "text/plain; charset=utf-8", "Allow": "GET, HEAD"],
                    body: Data("method not allowed".utf8)
                )
            }
        } else {
            response = Response(
                status: 400,
                headers: ["Content-Type": "text/plain; charset=utf-8"],
                body: Data("bad request".utf8)
            )
        }

        let head = Self.serializeHead(response)
        connection.send(content: head, completion: .contentProcessed { [weak self] error in
            guard error == nil, let self else {
                connection.cancel()
                return
            }
            self.sendBody(response.body, from: response.body.startIndex, on: connection)
        })
    }

    /// Sends the body a chunk at a time. The emulator wasm runs to a hundred
    /// megabytes or more; handing that to a single `send` costs a full extra
    /// copy of it, which is exactly the kind of spike that gets a webview-heavy
    /// app jetsammed.
    private static let chunkSize = 1 << 20

    private func sendBody(_ body: Data, from index: Data.Index, on connection: NWConnection) {
        guard index < body.endIndex else {
            connection.send(content: nil, isComplete: true, completion: .contentProcessed { _ in
                connection.cancel()
            })
            return
        }

        let end = body.index(index, offsetBy: Self.chunkSize, limitedBy: body.endIndex) ?? body.endIndex
        connection.send(content: Data(body[index..<end]), completion: .contentProcessed { [weak self] error in
            guard error == nil, let self else {
                connection.cancel()
                return
            }
            self.sendBody(body, from: end, on: connection)
        })
    }

    // MARK: - Parsing / serialization (pure, unit-tested)

    static func headerTerminator(in data: Data) -> Data.Index? {
        let pattern = Data("\r\n\r\n".utf8)
        guard data.count >= pattern.count else { return nil }
        return data.range(of: pattern)?.lowerBound
    }

    static func parseRequest(_ head: String) -> Request? {
        let lines = head.components(separatedBy: "\r\n")
        guard let requestLine = lines.first else { return nil }
        let parts = requestLine.split(separator: " ", omittingEmptySubsequences: true)
        guard parts.count >= 2 else { return nil }

        let method = String(parts[0]).uppercased()
        let target = String(parts[1])

        var path = target
        var query: [String: String] = [:]
        if let questionMark = target.firstIndex(of: "?") {
            path = String(target[..<questionMark])
            let rawQuery = String(target[target.index(after: questionMark)...])
            for pair in rawQuery.split(separator: "&") {
                let keyValue = pair.split(separator: "=", maxSplits: 1, omittingEmptySubsequences: false)
                let key = String(keyValue[0]).removingPercentEncoding ?? String(keyValue[0])
                let value = keyValue.count > 1
                    ? (String(keyValue[1]).removingPercentEncoding ?? String(keyValue[1]))
                    : ""
                query[key] = value
            }
        }
        path = path.removingPercentEncoding ?? path

        var headers: [String: String] = [:]
        for line in lines.dropFirst() where !line.isEmpty {
            guard let colon = line.firstIndex(of: ":") else { continue }
            let name = String(line[..<colon]).trimmingCharacters(in: .whitespaces).lowercased()
            let value = String(line[line.index(after: colon)...]).trimmingCharacters(in: .whitespaces)
            headers[name] = value
        }

        return Request(method: method, path: path, query: query, headers: headers)
    }

    static func serializeHead(_ response: Response) -> Data {
        var headers = response.headers
        for (name, value) in isolationHeaders where headers[name] == nil {
            headers[name] = value
        }
        headers["Content-Length"] = headers["Content-Length"] ?? String(response.body.count)
        headers["Connection"] = "close"

        var head = "HTTP/1.1 \(response.status) \(reasonPhrase(response.status))\r\n"
        for name in headers.keys.sorted() {
            head += "\(name): \(headers[name] ?? "")\r\n"
        }
        head += "\r\n"
        return Data(head.utf8)
    }

    /// The whole response in one buffer. Only tests use this; the server sends
    /// the head and then streams the body.
    static func serialize(_ response: Response) -> Data {
        var out = serializeHead(response)
        out.append(response.body)
        return out
    }

    static func reasonPhrase(_ status: Int) -> String {
        switch status {
        case 200: return "OK"
        case 400: return "Bad Request"
        case 404: return "Not Found"
        case 405: return "Method Not Allowed"
        case 500: return "Internal Server Error"
        default: return "Status"
        }
    }

    static func contentType(forPathExtension pathExtension: String) -> String {
        switch pathExtension.lowercased() {
        case "html", "htm": return "text/html; charset=utf-8"
        case "js", "mjs": return "text/javascript; charset=utf-8"
        case "json": return "application/json"
        case "wasm": return "application/wasm"
        case "css": return "text/css; charset=utf-8"
        case "txt": return "text/plain; charset=utf-8"
        case "gz", "gzip": return "application/gzip"
        default: return "application/octet-stream"
        }
    }
}

enum LoopbackServerError: Error, LocalizedError {
    case noPort
    case cancelled

    var errorDescription: String? {
        switch self {
        case .noPort:
            return "Loopback server started without a port"
        case .cancelled:
            return "Loopback server was cancelled"
        }
    }
}

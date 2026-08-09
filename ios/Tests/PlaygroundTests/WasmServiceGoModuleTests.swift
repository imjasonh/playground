import XCTest

@testable import Playground

/// The end-to-end demo, run on a simulator: a real Go `net/http` service,
/// compiled to wasip1, interpreted in-process, answering a real HTTP request
/// over a real socket.
///
/// The module is `wasm-hello`, built by `ios.yml` and dropped into
/// `Tests/Fixtures`. It is several megabytes and deliberately not in git, so
/// these skip when it is absent — a plain checkout still builds and tests
/// green, and CI is where the whole path gets exercised.
final class WasmServiceGoModuleTests: XCTestCase {
    /// Interpreted wasm starting a Go runtime is slow, and a simulator on a
    /// shared CI runner is slower. These are generous on purpose: the question
    /// is whether it works at all, not whether it is quick.
    private let startupTimeout: TimeInterval = 120

    /// `Tests/Fixtures` is a folder reference, so the module lands in a
    /// subdirectory of the bundle rather than at its root. The flat lookup is
    /// the fallback for anyone who drops the file in by hand.
    private func goModule() throws -> Data {
        let bundle = Bundle(for: Self.self)
        let url = bundle.url(forResource: "hello", withExtension: "wasm", subdirectory: "Fixtures")
            ?? bundle.url(forResource: "hello", withExtension: "wasm")
        guard let url else {
            throw XCTSkip(
                "hello.wasm is not bundled. Build it with "
                    + "`cd wasm-hello && GOOS=wasip1 GOARCH=wasm go build -buildmode=c-shared "
                    + "-o ../ios/Tests/Fixtures/hello.wasm .` and re-run."
            )
        }
        return try Data(contentsOf: url)
    }

    // MARK: - Straight through the guest

    func testGoServiceAnswersThroughTheABI() throws {
        let guest = try WasmHTTPGuest(
            module: try goModule(),
            wasi: WASIHost(configuration: WASIHost.Configuration(), log: { print("[guest] \($0)") }),
            memoryLimit: 256 << 20
        )

        let response = try guest.handle(Data("GET / HTTP/1.1\r\nHost: phone.local\r\n\r\n".utf8))
        let text = String(decoding: response, as: UTF8.self)

        XCTAssertTrue(text.hasPrefix("HTTP/1.1 200 OK\r\n"), "unexpected response:\n\(text)")
        XCTAssertTrue(text.contains("Hello from Go"), "unexpected body:\n\(text)")
        XCTAssertTrue(text.contains("wasip1/wasm"), "the guest does not think it is wasip1:\n\(text)")
    }

    /// The instance is supposed to outlive the request — that is what a
    /// reactor module buys, and what keeps the Go runtime from starting over
    /// on every hit. The guest's own counter is the evidence.
    func testGoInstanceIsReusedAcrossRequests() throws {
        let guest = try WasmHTTPGuest(
            module: try goModule(),
            wasi: WASIHost(configuration: WASIHost.Configuration(), log: { _ in }),
            memoryLimit: 256 << 20
        )

        var counts: [Int] = []
        for _ in 0..<3 {
            let response = try guest.handle(Data("GET /info HTTP/1.1\r\nHost: phone\r\n\r\n".utf8))
            counts.append(try requestCount(in: response))
        }

        XCTAssertEqual(counts, [1, 2, 3], "the guest is being re-instantiated per request")
    }

    // MARK: - Over a socket

    func testGoServiceAnswersOverTCP() async throws {
        let module = try goModule()
        let runtime = WasmServiceRuntime()
        defer { runtime.stop() }

        let started = try await runtime.start(
            module: module,
            configuration: WasmServiceRuntime.Configuration(
                // Port 0 asks the system for a free one, so a busy 8080 on the
                // runner cannot make this flaky. Bound on every interface
                // rather than loopback-only, because pinning the local
                // endpoint is what makes an ephemeral port ambiguous — and
                // 127.0.0.1 reaches it either way.
                port: 0,
                loopbackOnly: false
            )
        )
        XCTAssertGreaterThan(started.port, 0)

        let url = try XCTUnwrap(URL(string: "http://127.0.0.1:\(started.port)/healthz"))
        var request = URLRequest(url: url)
        request.timeoutInterval = startupTimeout

        let (data, response) = try await URLSession.shared.data(for: request)
        let http = try XCTUnwrap(response as? HTTPURLResponse)

        XCTAssertEqual(http.statusCode, 200)
        XCTAssertEqual(String(decoding: data, as: UTF8.self), "ok\n")
    }

    // MARK: - Helpers

    private func requestCount(in response: Data) throws -> Int {
        let text = String(decoding: response, as: UTF8.self)
        guard let separator = text.range(of: "\r\n\r\n") else {
            throw Failure.noBody(text)
        }
        let body = Data(text[separator.upperBound...].utf8)
        let decoded = try JSONSerialization.jsonObject(with: body) as? [String: Any]
        guard let count = decoded?["requests"] as? Int else {
            throw Failure.noBody(text)
        }
        return count
    }

    private enum Failure: Error {
        case noBody(String)
    }
}

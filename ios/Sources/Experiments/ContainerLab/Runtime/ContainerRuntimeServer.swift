import Foundation

/// Where the wasm runtime (emulator + kernel + JS glue) lives once it is
/// bundled into the app.
///
/// It is deliberately *bundled*, never downloaded: App Review's tolerance for
/// apps like this rests on the interpreter shipping inside the reviewed binary
/// and only the user's image arriving at runtime as data.
enum RuntimeAssets {
    static let directoryName = "ContainerRuntime"
    static let entryPointName = "index.html"
    /// The emulator itself, produced by `c2w --to-js` and installed by
    /// `ios/ContainerRuntime/fetch-runtime.sh`. It is not in git, so the page
    /// can be present while the emulator is not.
    static let emulatorName = "out.wasm"

    static var rootURL: URL? {
        Bundle.main.url(forResource: directoryName, withExtension: nil)
    }

    static func has(_ name: String) -> Bool {
        guard let rootURL else { return false }
        return FileManager.default.fileExists(atPath: rootURL.appendingPathComponent(name).path)
    }

    static var hasPage: Bool { has(entryPointName) }

    static var isInstalled: Bool { hasPage && has(emulatorName) }

    /// Shown in the UI so the missing piece is obvious rather than mysterious.
    static var status: String {
        if isInstalled {
            return "Bundled wasm runtime found"
        }
        if hasPage {
            return "Runtime page bundled, emulator missing (out.wasm) — pull and inspect work, execution does not"
        }
        return "No wasm runtime bundled — pull and inspect work, execution does not"
    }
}

/// Serves everything the runtime webview needs from one loopback origin:
/// the bundled runtime assets, the materialized image layout, and the
/// isolation probe page.
///
/// One origin for all of it is the point — the webview never makes a
/// cross-origin request, so `require-corp` never blocks a subresource and no
/// CORS proxy is involved. It also means registry authentication stays on the
/// native side, which is what makes private and Docker Hub images work at all
/// (container2wasm's in-browser puller supports neither auth nor
/// CORS-less registries).
final class ContainerRuntimeServer {
    enum Route {
        static let probe = "/probe.html"
        static let image = "/image/"
        static let runtime = "/runtime/"
    }

    private var server: LoopbackServer?
    /// Read from the network queue, written from the UI, so it gets a lock.
    private let imageRootLock = NSLock()
    private var storedImageRoot: URL?

    private var imageRoot: URL? {
        get {
            imageRootLock.lock()
            defer { imageRootLock.unlock() }
            return storedImageRoot
        }
        set {
            imageRootLock.lock()
            storedImageRoot = newValue
            imageRootLock.unlock()
        }
    }

    var baseURL: URL? { server?.baseURL }

    var probeURL: URL? {
        guard let baseURL else { return nil }
        return baseURL.appendingPathComponent("probe.html")
    }

    func start(imageRoot: URL? = nil) async throws -> URL {
        self.imageRoot = imageRoot

        if let server, let baseURL = server.baseURL {
            return baseURL
        }

        let server = LoopbackServer { [weak self] request in
            self?.respond(to: request) ?? .notFound()
        }
        _ = try await server.start()
        self.server = server

        guard let baseURL = server.baseURL else {
            throw LoopbackServerError.noPort
        }
        return baseURL
    }

    func update(imageRoot: URL?) {
        self.imageRoot = imageRoot
    }

    func stop() {
        server?.stop()
        server = nil
    }

    // MARK: - Routing

    private func respond(to request: LoopbackServer.Request) -> LoopbackServer.Response {
        let path = request.path

        if path == "/" || path == Route.probe {
            if path == "/", RuntimeAssets.hasPage, let root = RuntimeAssets.rootURL {
                return serveFile(relativePath: RuntimeAssets.entryPointName, under: root)
            }
            return LoopbackServer.Response.data(
                Data(RuntimeProbePage.html.utf8),
                contentType: "text/html; charset=utf-8"
            )
        }

        if path.hasPrefix(Route.image) {
            guard let imageRoot else { return .notFound() }
            return serveFile(relativePath: String(path.dropFirst(Route.image.count)), under: imageRoot)
        }

        if path.hasPrefix(Route.runtime) {
            guard let runtimeRoot = RuntimeAssets.rootURL else { return .notFound() }
            return serveFile(relativePath: String(path.dropFirst(Route.runtime.count)), under: runtimeRoot)
        }

        if RuntimeAssets.hasPage, let runtimeRoot = RuntimeAssets.rootURL {
            return serveFile(relativePath: String(path.dropFirst()), under: runtimeRoot)
        }

        return .notFound()
    }

    /// Maps a request path to a file inside `root`, or nil when it would escape.
    static func resolvedFileURL(relativePath: String, under root: URL) -> URL? {
        guard !relativePath.isEmpty else { return nil }

        let components = relativePath.split(separator: "/").map(String.init)
        guard !components.contains(".."), !components.contains(".") else { return nil }

        var url = root
        for component in components {
            url.appendPathComponent(component)
        }

        let rootPath = root.standardizedFileURL.path
        let candidate = url.standardizedFileURL.path
        guard candidate.hasPrefix(rootPath + "/") else { return nil }
        return url
    }

    /// Serves a file, refusing anything that escapes the root.
    private func serveFile(relativePath: String, under root: URL) -> LoopbackServer.Response {
        guard let url = Self.resolvedFileURL(relativePath: relativePath, under: root) else {
            return .notFound()
        }

        var isDirectory: ObjCBool = false
        guard FileManager.default.fileExists(atPath: url.path, isDirectory: &isDirectory),
              !isDirectory.boolValue,
              let data = try? Data(contentsOf: url, options: .mappedIfSafe) else {
            return .notFound()
        }

        return LoopbackServer.Response(
            status: 200,
            headers: [
                "Content-Type": LoopbackServer.contentType(forPathExtension: url.pathExtension),
                "Accept-Ranges": "none"
            ],
            body: data
        )
    }
}

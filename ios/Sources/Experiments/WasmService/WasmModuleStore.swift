import Foundation

/// Where a pulled module lives between runs.
///
/// The cache exists for one reason: a background window can start with the app
/// freshly relaunched and no network worth relying on, so "resume the service"
/// has to mean reading a file, not pulling a registry. Blobs are stored under
/// their digest, which the registry client has already verified, so a cache
/// hit is exactly the bytes the manifest named.
struct WasmModuleStore {
    static let shared = WasmModuleStore()

    /// The reference and digest last started, so a relaunch knows what to
    /// bring back up.
    struct Record: Codable, Equatable {
        var reference: String
        var digest: String
        var port: UInt16
    }

    private let recordKey = "wasmservice.lastModule"
    private let defaults: UserDefaults
    private let fileManager: FileManager

    init(defaults: UserDefaults = .standard, fileManager: FileManager = .default) {
        self.defaults = defaults
        self.fileManager = fileManager
    }

    /// Application Support rather than Caches: a module the user asked to keep
    /// serving should not evaporate under storage pressure while the service
    /// is meant to be running.
    private var directory: URL? {
        guard
            let base = fileManager.urls(for: .applicationSupportDirectory, in: .userDomainMask).first
        else { return nil }
        return base.appendingPathComponent("WasmService", isDirectory: true)
    }

    func url(forDigest digest: String) -> URL? {
        guard let directory else { return nil }
        return directory.appendingPathComponent(Self.fileName(forDigest: digest))
    }

    @discardableResult
    func save(_ module: Data, digest: String) throws -> URL {
        guard let directory, let url = url(forDigest: digest) else {
            throw StoreError.noDirectory
        }
        try fileManager.createDirectory(at: directory, withIntermediateDirectories: true)
        try module.write(to: url, options: .atomic)
        return url
    }

    func load(digest: String) -> Data? {
        guard let url = url(forDigest: digest) else { return nil }
        return try? Data(contentsOf: url)
    }

    var lastRecord: Record? {
        get {
            guard let data = defaults.data(forKey: recordKey) else { return nil }
            return try? JSONDecoder().decode(Record.self, from: data)
        }
        nonmutating set {
            guard let newValue, let encoded = try? JSONEncoder().encode(newValue) else {
                defaults.removeObject(forKey: recordKey)
                return
            }
            defaults.set(encoded, forKey: recordKey)
        }
    }

    /// `sha256:abcd…` is not a filename on every filesystem, and the algorithm
    /// prefix carries no information once it is in this directory.
    ///
    /// Anything that is not hex all the way through falls back to one shared
    /// name rather than being filtered down to its hex characters: filtering
    /// would silently map two different digests onto the same file. A digest
    /// that reaches here has already been verified by the registry client, so
    /// the fallback is for hand-written input only.
    static func fileName(forDigest digest: String) -> String {
        let hex = digest.split(separator: ":").last.map(String.init) ?? digest
        guard !hex.isEmpty, hex.allSatisfy(\.isHexDigit) else { return "module.wasm" }
        return hex + ".wasm"
    }

    enum StoreError: Error, LocalizedError {
        case noDirectory

        var errorDescription: String? {
            switch self {
            case .noDirectory:
                return "Could not find Application Support to cache the module in"
            }
        }
    }
}

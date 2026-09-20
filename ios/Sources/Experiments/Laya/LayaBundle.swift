import CryptoKit
import Foundation

/// `coreml_config.json` at the bundle root.
struct LayaManifest: Decodable {
    struct FileEntry: Decodable {
        let sha256: String?
    }

    struct Shape: Decodable {
        let batchSize: Int
        let maxLength: Int
        let maxOptions: Int
        let flexible: Bool?

        enum CodingKeys: String, CodingKey {
            case batchSize = "batch_size"
            case maxLength = "max_length"
            case maxOptions = "max_options"
            case flexible
        }
    }

    let format: String
    let formatVersion: Int?
    let shape: Shape
    let files: [String: FileEntry]?

    enum CodingKeys: String, CodingKey {
        case format
        case formatVersion = "format_version"
        case shape
        case files
    }

    static let aneFormat = "laya-coreml-ane"

    /// Same gate as `ANEAgent.__init__`.
    func validateANE() throws {
        guard format == Self.aneFormat, formatVersion == 1 else {
            throw LayaError.bundle("Unsupported ANE bundle format (\(format) v\(formatVersion ?? 0)).")
        }
        guard shape.batchSize == 1, shape.maxOptions == 32, shape.flexible != true else {
            throw LayaError.bundle("ANE runtime requires a fixed B1/K32 bundle.")
        }
    }

    var layaShape: LayaShape {
        LayaShape(batchSize: shape.batchSize, maxLength: shape.maxLength, maxOptions: shape.maxOptions)
    }
}

/// `rl_agent_config.json`: prompt caps and calibration.
struct LayaAgentConfig: Decodable {
    var maxLength = 512
    var headMaxLength = 192
    var temperature: [Double] = [1, 1, 1]
    var temperatureByOptions: [String: Double] = [:]

    enum CodingKeys: String, CodingKey {
        case maxLength = "max_len"
        case headMaxLength = "head_max_len"
        case temperature
        case temperatureByOptions = "temperature_by_options"
    }

    init() {}

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        maxLength = try container.decodeIfPresent(Int.self, forKey: .maxLength) ?? 512
        headMaxLength = try container.decodeIfPresent(Int.self, forKey: .headMaxLength) ?? 192
        temperature = try container.decodeIfPresent([Double].self, forKey: .temperature) ?? [1, 1, 1]
        temperatureByOptions = try container.decodeIfPresent([String: Double].self, forKey: .temperatureByOptions) ?? [:]
    }

    var calibration: LayaCalibration {
        LayaCalibration(temperature: temperature, temperatureByOptions: temperatureByOptions)
    }
}

/// `encoder/config.json`: the two fields the host needs.
struct LayaEncoderConfig: Decodable {
    let hiddenSize: Int
    var localAttention = 128

    enum CodingKeys: String, CodingKey {
        case hiddenSize = "hidden_size"
        case localAttention = "local_attention"
    }

    init(hiddenSize: Int, localAttention: Int = 128) {
        self.hiddenSize = hiddenSize
        self.localAttention = localAttention
    }

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        hiddenSize = try container.decode(Int.self, forKey: .hiddenSize)
        localAttention = try container.decodeIfPresent(Int.self, forKey: .localAttention) ?? 128
    }
}

/// The four special tokens `tokenizer_config.json` names. Values are either a
/// string or an added-token object with `content`.
struct LayaSpecialTokens: Equatable {
    let cls: String
    let sep: String
    let pad: String
    let mask: String

    init(cls: String, sep: String, pad: String, mask: String) {
        self.cls = cls
        self.sep = sep
        self.pad = pad
        self.mask = mask
    }

    init(tokenizerConfig data: Data) throws {
        let raw = try JSONSerialization.jsonObject(with: data)
        guard let object = raw as? [String: Any] else {
            throw LayaError.bundle("tokenizer_config.json is not a JSON object.")
        }
        func token(_ key: String) throws -> String {
            let value = object[key]
            if let string = value as? String {
                return string
            }
            if let added = value as? [String: Any], let content = added["content"] as? String {
                return content
            }
            throw LayaError.bundle("Tokenizer is missing a valid \(key)")
        }
        self.init(
            cls: try token("cls_token"),
            sep: try token("sep_token"),
            pad: try token("pad_token"),
            mask: try token("mask_token")
        )
    }
}

/// File names inside a downloaded bundle.
enum LayaBundleFile {
    static let manifest = "coreml_config.json"
    static let agentConfig = "rl_agent_config.json"
    static let encoderConfig = "encoder/config.json"
    static let tokenizerDirectory = "tokenizer"
    static let tokenizerConfig = "tokenizer/tokenizer_config.json"
    static let package = "model.mlpackage"
    static let hostWeights = "host_weights.safetensors"

    /// Globs passed to the Hub snapshot; same allow list as `hub.py`.
    static let downloadGlobs = [
        manifest,
        agentConfig,
        encoderConfig,
        "tokenizer/*",
        "model.mlpackage/*",
        hostWeights,
    ]
}

/// Reads and checks the JSON side of a downloaded bundle.
struct LayaBundle {
    let root: URL
    let manifest: LayaManifest
    let agentConfig: LayaAgentConfig
    let encoderConfig: LayaEncoderConfig
    let specialTokens: LayaSpecialTokens

    var packageURL: URL { root.appendingPathComponent(LayaBundleFile.package) }
    var hostWeightsURL: URL { root.appendingPathComponent(LayaBundleFile.hostWeights) }
    var tokenizerURL: URL { root.appendingPathComponent(LayaBundleFile.tokenizerDirectory) }

    init(root: URL) throws {
        self.root = root
        let decoder = JSONDecoder()
        manifest = try decoder.decode(LayaManifest.self, from: try Self.read(root, LayaBundleFile.manifest))
        try manifest.validateANE()
        agentConfig = try decoder.decode(LayaAgentConfig.self, from: try Self.read(root, LayaBundleFile.agentConfig))
        encoderConfig = try decoder.decode(LayaEncoderConfig.self, from: try Self.read(root, LayaBundleFile.encoderConfig))
        specialTokens = try LayaSpecialTokens(tokenizerConfig: try Self.read(root, LayaBundleFile.tokenizerConfig))
        for name in [LayaBundleFile.package, LayaBundleFile.hostWeights] {
            guard FileManager.default.fileExists(atPath: root.appendingPathComponent(name).path) else {
                throw LayaError.bundle("Bundle is missing \(name).")
            }
        }
    }

    private static func read(_ root: URL, _ name: String) throws -> Data {
        let url = root.appendingPathComponent(name)
        guard FileManager.default.fileExists(atPath: url.path) else {
            throw LayaError.bundle("Bundle is missing \(name).")
        }
        return try Data(contentsOf: url)
    }

    /// `verify_files`: every manifest entry with a digest must match on disk.
    func verifyFiles() throws {
        for (name, entry) in manifest.files ?? [:] {
            guard let expected = entry.sha256 else { continue }
            let parts = name.split(separator: "/", omittingEmptySubsequences: false)
            guard !name.hasPrefix("/"), !name.contains("\\"), !parts.contains("..") else {
                throw LayaError.bundle("Bundle file names must be relative paths inside the model directory.")
            }
            let url = root.appendingPathComponent(name)
            guard FileManager.default.fileExists(atPath: url.path) else {
                throw LayaError.bundle("Bundle is missing \(name).")
            }
            let actual = try Self.sha256Hex(of: url)
            guard actual == expected.lowercased() else {
                throw LayaError.bundle("Checksum mismatch for \(name).")
            }
        }
    }

    static func sha256Hex(of url: URL) throws -> String {
        let handle = try FileHandle(forReadingFrom: url)
        defer { try? handle.close() }
        var hasher = SHA256()
        while true {
            let chunk = try handle.read(upToCount: 4 << 20) ?? Data()
            if chunk.isEmpty { break }
            hasher.update(data: chunk)
        }
        return hasher.finalize().map { String(format: "%02x", $0) }.joined()
    }
}

import Foundation

/// Minimal HTTP surface so tests can substitute a fake.
protocol AppAttestHTTPClient: Sendable {
    func data(for request: URLRequest) async throws -> (Data, URLResponse)
}

extension URLSession: AppAttestHTTPClient {}

/// HTTP client for the `app-attest` Cloudflare Worker.
struct AppAttestAPI: Sendable {
    var baseURL: URL
    var http: any AppAttestHTTPClient

    init(
        baseURL: URL = AppAttestAPI.defaultBaseURL,
        http: any AppAttestHTTPClient = URLSession.shared
    ) {
        self.baseURL = baseURL
        self.http = http
    }

    static let defaultBaseURL: URL = {
        if let url = URL(string: "https://app-attest.imjasonh.workers.dev") {
            return url
        }
        return URL(fileURLWithPath: "/invalid-app-attest-url")
    }()

    func fetchChallenge() async throws -> AppAttestChallenge {
        try await post(path: "v1/challenge", body: Data("{}".utf8))
    }

    func register(
        keyId: String,
        attestationObject: Data,
        clientDataJSON: Data
    ) async throws -> AppAttestRegisterResponse {
        guard let clientData = String(data: clientDataJSON, encoding: .utf8) else {
            throw AppAttestAPIError.invalidClientData
        }
        let body = AppAttestRegisterRequest(
            keyId: keyId,
            attestationObject: attestationObject.base64EncodedString(),
            clientData: clientData
        )
        return try await post(path: "v1/token", body: try JSONEncoder().encode(body))
    }

    func registerUnattested(clientDataJSON: Data) async throws -> AppAttestRegisterResponse {
        guard let clientData = String(data: clientDataJSON, encoding: .utf8) else {
            throw AppAttestAPIError.invalidClientData
        }
        let body = AppAttestUnattestedRequest(clientData: clientData)
        return try await post(path: "v1/unattested-token", body: try JSONEncoder().encode(body))
    }

    func whoami(
        keyId: String,
        assertionObject: Data?,
        clientDataJSON: Data
    ) async throws -> AppAttestWhoAmI {
        guard let clientData = String(data: clientDataJSON, encoding: .utf8) else {
            throw AppAttestAPIError.invalidClientData
        }
        let body = AppAttestWhoAmIRequest(
            keyId: keyId,
            assertionObject: assertionObject?.base64EncodedString(),
            clientData: clientData
        )
        return try await post(path: "v1/whoami", body: try JSONEncoder().encode(body))
    }

    private func post<T: Decodable>(path: String, body: Data) async throws -> T {
        var request = URLRequest(url: baseURL.appending(path: path))
        request.httpMethod = "POST"
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        request.httpBody = body
        return try await send(request)
    }

    private func send<T: Decodable>(_ request: URLRequest) async throws -> T {
        let (data, response) = try await http.data(for: request)
        let status = (response as? HTTPURLResponse)?.statusCode ?? 0
        if (200..<300).contains(status) {
            return try JSONDecoder().decode(T.self, from: data)
        }
        if let err = try? JSONDecoder().decode(AppAttestAPIErrorBody.self, from: data) {
            throw AppAttestAPIError.server(status: status, message: err.error)
        }
        throw AppAttestAPIError.http(status)
    }
}

struct AppAttestChallenge: Decodable, Equatable {
    var challenge: String
    var expiresAt: UInt64
}

struct AppAttestRegisterRequest: Encodable {
    var keyId: String
    var attestationObject: String
    var clientData: String
}

struct AppAttestUnattestedRequest: Encodable {
    var clientData: String
}

struct AppAttestWhoAmIRequest: Encodable {
    var keyId: String
    var assertionObject: String?
    var clientData: String

    enum CodingKeys: String, CodingKey {
        case keyId, assertionObject, clientData
    }

    func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(keyId, forKey: .keyId)
        try container.encodeIfPresent(assertionObject, forKey: .assertionObject)
        try container.encode(clientData, forKey: .clientData)
    }
}

struct AppAttestRegisterResponse: Decodable, Equatable {
    var userId: String
    var deviceId: String
    var keyId: String
    var unattested: Bool
    var counter: UInt32?
    var riskMetric: UInt32?
}

struct AppAttestWhoAmI: Decodable, Equatable {
    var userId: String
    var deviceId: String
    var keyId: String
    var unattested: Bool
    var counter: UInt32?
    var riskMetric: UInt32?
}

struct AppAttestAPIErrorBody: Decodable {
    var error: String
}

enum AppAttestAPIError: Error, Equatable, LocalizedError {
    case http(Int)
    case server(status: Int, message: String)
    case invalidClientData

    var errorDescription: String? {
        switch self {
        case .http(let status):
            return "Worker returned HTTP \(status)."
        case .server(_, let message):
            return message
        case .invalidClientData:
            return "clientData is not UTF-8."
        }
    }
}

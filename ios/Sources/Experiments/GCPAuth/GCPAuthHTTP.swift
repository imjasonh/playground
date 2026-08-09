import Foundation

/// Seam between the credential chain and the network, so tests (and the
/// simulated mode this experiment ships with) can answer without a project.
protocol GCPAuthTransport {
    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse)
}

struct GCPAuthURLSessionTransport: GCPAuthTransport {
    let session: URLSession

    init(session: URLSession = .shared) {
        self.session = session
    }

    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse) {
        let (data, response) = try await session.data(for: request)
        guard let http = response as? HTTPURLResponse else {
            throw GCPAuthError.malformedResponse("Expected an HTTP response.")
        }
        return (data, http)
    }
}

/// Thin JSON/form client that understands Google's error envelope.
struct GCPAuthHTTPClient {
    let transport: GCPAuthTransport

    func postJSON<Body: Encodable, Response: Decodable>(
        url: URL,
        body: Body,
        headers: [String: String] = [:]
    ) async throws -> Response {
        var request = URLRequest(url: url)
        request.httpMethod = "POST"
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        for (name, value) in headers {
            request.setValue(value, forHTTPHeaderField: name)
        }
        request.httpBody = try JSONEncoder().encode(body)
        return try await send(request)
    }

    func postForm<Response: Decodable>(
        url: URL,
        fields: [(String, String)],
        headers: [String: String] = [:]
    ) async throws -> Response {
        var request = URLRequest(url: url)
        request.httpMethod = "POST"
        request.setValue("application/x-www-form-urlencoded", forHTTPHeaderField: "Content-Type")
        for (name, value) in headers {
            request.setValue(value, forHTTPHeaderField: name)
        }
        request.httpBody = GCPAuthForm.body(fields)
        return try await send(request)
    }

    private func send<Response: Decodable>(_ request: URLRequest) async throws -> Response {
        let (data, http) = try await transport.send(request)
        guard (200..<300).contains(http.statusCode) else {
            throw GCPAuthError.http(status: http.statusCode, message: Self.errorMessage(from: data))
        }
        do {
            return try JSONDecoder().decode(Response.self, from: data)
        } catch {
            throw GCPAuthError.malformedResponse(
                "Could not decode \(Response.self) from \(data.count) bytes."
            )
        }
    }

    /// Google returns `{"error": {"code": …, "message": …, "status": …}}` on
    /// failure; fall back to the raw body when it doesn't.
    static func errorMessage(from data: Data) -> String {
        if let envelope = try? JSONDecoder().decode(GoogleErrorEnvelope.self, from: data),
           let message = envelope.error.message,
           !message.isEmpty {
            return message
        }
        let raw = String(decoding: data, as: UTF8.self)
            .trimmingCharacters(in: .whitespacesAndNewlines)
        return String(raw.prefix(300))
    }

    private struct GoogleErrorEnvelope: Decodable {
        struct Body: Decodable {
            let code: Int?
            let message: String?
            let status: String?
        }

        let error: Body
    }
}

enum GCPAuthURLBuilder {
    /// Google REST "custom methods" hang off the resource path after a colon
    /// (`…/apps/1:2:ios:3:exchangeAppAttestAssertion`), and the API key rides in
    /// the query string.
    static func googleAPI(
        host: String,
        path: String,
        apiKey: String? = nil
    ) throws -> URL {
        var string = "https://\(host)/\(path)"
        if let apiKey, !apiKey.isEmpty {
            string += "?key=\(GCPAuthForm.percentEncode(apiKey))"
        }
        guard let url = URL(string: string) else {
            throw GCPAuthError.badURL(string)
        }
        return url
    }
}

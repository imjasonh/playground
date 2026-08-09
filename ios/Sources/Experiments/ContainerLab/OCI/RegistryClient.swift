import Foundation

/// Seam so tests can drive the client without a network.
protocol HTTPTransport {
    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse)
}

struct URLSessionTransport: HTTPTransport {
    let session: URLSession

    init(session: URLSession = .shared) {
        self.session = session
    }

    func send(_ request: URLRequest) async throws -> (Data, HTTPURLResponse) {
        let (data, response) = try await session.data(for: request)
        guard let http = response as? HTTPURLResponse else {
            throw RegistryError.notHTTP
        }
        return (data, http)
    }
}

enum RegistryError: Error, LocalizedError {
    case notHTTP
    case badStatus(code: Int, body: String)
    case unauthorized(String)
    case unsupportedManifest(String)
    case noMatchingPlatform(OCIPlatform)
    case malformedResponse(String)

    var errorDescription: String? {
        switch self {
        case .notHTTP:
            return "Registry returned a non-HTTP response"
        case .badStatus(let code, let body):
            let detail = body.isEmpty ? "" : " — \(body.prefix(200))"
            return "Registry returned HTTP \(code)\(detail)"
        case .unauthorized(let detail):
            return "Registry authentication failed: \(detail)"
        case .unsupportedManifest(let mediaType):
            return "Unsupported manifest type \(mediaType). Docker schema 1 images are not supported."
        case .noMatchingPlatform(let platform):
            return "This image has no \(platform.displayName) manifest"
        case .malformedResponse(let detail):
            return "Malformed registry response: \(detail)"
        }
    }
}

/// A read-only OCI distribution client: resolve a reference to one platform's
/// manifest, then pull config and layer blobs with digest verification.
///
/// Anonymous pull only for now (the Docker Hub / GHCR public path). Tokens are
/// cached per scope for the lifetime of the client.
actor RegistryClient {
    private let transport: HTTPTransport
    private var tokensByScope: [String: String] = [:]

    init(transport: HTTPTransport = URLSessionTransport()) {
        self.transport = transport
    }

    // MARK: - Resolution

    func resolve(_ reference: ImageReference, platform: OCIPlatform) async throws -> ResolvedImage {
        let (topData, topResponse) = try await getManifest(reference, reference: reference.apiReference)
        let topMediaType = mediaType(of: topData, response: topResponse)

        var manifestData = topData
        var manifestDescriptor = OCIDescriptor(
            mediaType: topMediaType ?? OCIMediaType.ociManifest,
            digest: topResponse.value(forHTTPHeaderField: "Docker-Content-Digest")
                ?? OCIDigest.sha256(of: topData),
            size: Int64(topData.count),
            platform: nil,
            annotations: nil
        )

        if OCIMediaType.isIndex(topMediaType) {
            let index = try decode(OCIIndex.self, from: topData, what: "index")
            guard let selected = PlatformMatcher.select(from: index, matching: platform) else {
                throw RegistryError.noMatchingPlatform(platform)
            }
            let (childData, childResponse) = try await getManifest(reference, reference: selected.digest)
            try OCIDigest.verify(childData, matches: selected.digest)
            manifestData = childData
            manifestDescriptor = selected
            if manifestDescriptor.mediaType.isEmpty {
                manifestDescriptor.mediaType = mediaType(of: childData, response: childResponse)
                    ?? OCIMediaType.ociManifest
            }
        } else if !OCIMediaType.isManifest(topMediaType) && topMediaType != nil {
            throw RegistryError.unsupportedManifest(topMediaType ?? "unknown")
        }

        let manifest = try decode(OCIManifest.self, from: manifestData, what: "manifest")
        let configData = try await fetchBlob(manifest.config, from: reference)
        let config = try decode(OCIImageConfig.self, from: configData, what: "image config")

        return ResolvedImage(
            reference: reference,
            manifestDescriptor: manifestDescriptor,
            manifestData: manifestData,
            manifest: manifest,
            configData: configData,
            config: config
        )
    }

    // MARK: - Blobs

    /// Fetches a blob and verifies it against the descriptor's digest before
    /// handing it back. A blob that fails verification is never returned.
    func fetchBlob(_ descriptor: OCIDescriptor, from reference: ImageReference) async throws -> Data {
        let url = blobURL(reference, digest: descriptor.digest)
        let data = try await authorizedGet(url, reference: reference, accept: nil)
        try OCIDigest.verify(data, matches: descriptor.digest)
        return data
    }

    // MARK: - HTTP plumbing

    private func getManifest(
        _ reference: ImageReference,
        reference apiReference: String
    ) async throws -> (Data, HTTPURLResponse) {
        let url = manifestURL(reference, apiReference: apiReference)
        return try await authorizedRequest(url, reference: reference, accept: OCIMediaType.manifestAccept)
    }

    private func authorizedGet(_ url: URL, reference: ImageReference, accept: String?) async throws -> Data {
        try await authorizedRequest(url, reference: reference, accept: accept).0
    }

    private func authorizedRequest(
        _ url: URL,
        reference: ImageReference,
        accept: String?
    ) async throws -> (Data, HTTPURLResponse) {
        let scope = pullScope(for: reference)
        var request = URLRequest(url: url)
        request.httpMethod = "GET"
        if let accept {
            request.setValue(accept, forHTTPHeaderField: "Accept")
        }
        if let token = tokensByScope[scope] {
            request.setValue("Bearer \(token)", forHTTPHeaderField: "Authorization")
        }

        var (data, response) = try await transport.send(request)

        if response.statusCode == 401,
           let header = response.value(forHTTPHeaderField: "WWW-Authenticate"),
           let challenge = BearerChallenge.parse(header) {
            let token = try await requestToken(challenge: challenge, scope: scope)
            tokensByScope[scope] = token
            request.setValue("Bearer \(token)", forHTTPHeaderField: "Authorization")
            (data, response) = try await transport.send(request)
        }

        guard (200..<300).contains(response.statusCode) else {
            if response.statusCode == 401 || response.statusCode == 403 {
                throw RegistryError.unauthorized(String(data: data, encoding: .utf8) ?? "no detail")
            }
            throw RegistryError.badStatus(
                code: response.statusCode,
                body: String(data: data, encoding: .utf8) ?? ""
            )
        }
        return (data, response)
    }

    private func requestToken(challenge: BearerChallenge, scope: String) async throws -> String {
        guard let url = challenge.tokenURL(fallbackScope: scope) else {
            throw RegistryError.unauthorized("bad realm \(challenge.realm)")
        }
        var request = URLRequest(url: url)
        request.httpMethod = "GET"
        let (data, response) = try await transport.send(request)
        guard (200..<300).contains(response.statusCode) else {
            throw RegistryError.unauthorized("token endpoint returned HTTP \(response.statusCode)")
        }
        struct TokenResponse: Decodable {
            var token: String?
            var access_token: String?
        }
        let decoded = try decode(TokenResponse.self, from: data, what: "token")
        guard let token = decoded.token ?? decoded.access_token, !token.isEmpty else {
            throw RegistryError.unauthorized("token endpoint returned no token")
        }
        return token
    }

    // MARK: - Helpers

    private func pullScope(for reference: ImageReference) -> String {
        "repository:\(reference.repository):pull"
    }

    private func manifestURL(_ reference: ImageReference, apiReference: String) -> URL {
        registryURL(reference, path: "manifests/\(apiReference)")
    }

    private func blobURL(_ reference: ImageReference, digest: String) -> URL {
        registryURL(reference, path: "blobs/\(digest)")
    }

    private func registryURL(_ reference: ImageReference, path: String) -> URL {
        let scheme = reference.registryHost.hasPrefix("localhost") ? "http" : "https"
        // Force-unwrap is safe: every component is validated by ImageReference.
        return URL(string: "\(scheme)://\(reference.registryHost)/v2/\(reference.repository)/\(path)")!
    }

    private func mediaType(of data: Data, response: HTTPURLResponse) -> String? {
        if let header = response.value(forHTTPHeaderField: "Content-Type"),
           !header.isEmpty {
            return header.split(separator: ";").first.map {
                $0.trimmingCharacters(in: .whitespaces)
            }
        }
        // Fall back to the mediaType embedded in the document itself.
        struct MediaTypeProbe: Decodable { var mediaType: String? }
        return (try? JSONDecoder().decode(MediaTypeProbe.self, from: data))?.mediaType
    }

    private func decode<T: Decodable>(_ type: T.Type, from data: Data, what: String) throws -> T {
        do {
            return try JSONDecoder().decode(type, from: data)
        } catch {
            throw RegistryError.malformedResponse("\(what): \(error.localizedDescription)")
        }
    }
}

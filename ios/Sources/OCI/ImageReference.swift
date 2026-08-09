import Foundation

/// A parsed container image reference (`alpine`, `alpine:3.20`,
/// `ghcr.io/owner/name@sha256:…`).
///
/// Parsing follows the same rules the Docker/OCI clients use: the first path
/// component is a registry only when it looks like a host (contains `.` or `:`,
/// or is exactly `localhost`), Docker Hub gets the implicit `library/` prefix
/// for single-segment names, and a digest wins over a tag when both appear.
struct ImageReference: Equatable {
    /// Host used for registry API calls, e.g. `registry-1.docker.io`.
    let registryHost: String
    /// Host as the user wrote it (or the implied default), e.g. `docker.io`.
    let displayHost: String
    /// Full repository path, e.g. `library/alpine`.
    let repository: String
    let tag: String?
    let digest: String?

    static let defaultDisplayHost = "docker.io"
    static let dockerHubAPIHost = "registry-1.docker.io"

    /// What to put in the manifest URL path: a digest when pinned, else the tag.
    var apiReference: String {
        digest ?? tag ?? "latest"
    }

    /// Round-trippable canonical form, useful for display and logging.
    var canonicalName: String {
        let repo = displayHost == Self.defaultDisplayHost && repository.hasPrefix("library/")
            ? String(repository.dropFirst("library/".count))
            : repository
        let base = displayHost == Self.defaultDisplayHost ? repo : "\(displayHost)/\(repo)"
        if let digest {
            return "\(base)@\(digest)"
        }
        return "\(base):\(tag ?? "latest")"
    }

    init(registryHost: String, displayHost: String, repository: String, tag: String?, digest: String?) {
        self.registryHost = registryHost
        self.displayHost = displayHost
        self.repository = repository
        self.tag = tag
        self.digest = digest
    }

    init(parsing input: String) throws {
        let trimmed = input.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { throw ImageReferenceError.empty }

        var remainder = Substring(trimmed)
        var digest: String?
        if let atIndex = remainder.firstIndex(of: "@") {
            let candidate = String(remainder[remainder.index(after: atIndex)...])
            guard OCIDigest.isValid(candidate) else {
                throw ImageReferenceError.invalidDigest(candidate)
            }
            digest = candidate
            remainder = remainder[..<atIndex]
        }

        // A colon is a tag separator only when it comes after the last slash;
        // otherwise it is a registry port (`localhost:5000/foo`).
        var tag: String?
        let lastSlash = remainder.lastIndex(of: "/")
        if let colonIndex = remainder.lastIndex(of: ":"),
           lastSlash == nil || colonIndex > lastSlash! {
            let candidate = String(remainder[remainder.index(after: colonIndex)...])
            guard !candidate.isEmpty, candidate.allSatisfy({ $0.isLetter || $0.isNumber || "._-".contains($0) }) else {
                throw ImageReferenceError.invalidTag(candidate)
            }
            tag = candidate
            remainder = remainder[..<colonIndex]
        }

        var path = String(remainder)
        guard !path.isEmpty else { throw ImageReferenceError.empty }

        var displayHost = Self.defaultDisplayHost
        let components = path.split(separator: "/", omittingEmptySubsequences: false).map(String.init)
        if components.count > 1, Self.looksLikeRegistryHost(components[0]) {
            displayHost = components[0]
            path = components.dropFirst().joined(separator: "/")
        }

        guard !path.isEmpty, !path.contains("//") else {
            throw ImageReferenceError.invalidRepository(path)
        }
        guard path.allSatisfy({ $0.isLowercase || $0.isNumber || "._-/".contains($0) }) else {
            throw ImageReferenceError.invalidRepository(path)
        }

        let isDockerHub = displayHost == Self.defaultDisplayHost
            || displayHost == "index.docker.io"
            || displayHost == Self.dockerHubAPIHost
        if isDockerHub {
            displayHost = Self.defaultDisplayHost
            if !path.contains("/") {
                path = "library/\(path)"
            }
        }

        self.init(
            registryHost: isDockerHub ? Self.dockerHubAPIHost : displayHost,
            displayHost: displayHost,
            repository: path,
            tag: digest == nil ? (tag ?? "latest") : tag,
            digest: digest
        )
    }

    private static func looksLikeRegistryHost(_ candidate: String) -> Bool {
        if candidate == "localhost" { return true }
        if candidate.hasPrefix("localhost:") { return true }
        return candidate.contains(".") || candidate.contains(":")
    }
}

enum ImageReferenceError: Error, Equatable, LocalizedError {
    case empty
    case invalidTag(String)
    case invalidDigest(String)
    case invalidRepository(String)

    var errorDescription: String? {
        switch self {
        case .empty:
            return "Enter an image reference, for example alpine:3.20"
        case .invalidTag(let tag):
            return "“\(tag)” is not a valid tag"
        case .invalidDigest(let digest):
            return "“\(digest)” is not a valid digest"
        case .invalidRepository(let repository):
            return "“\(repository)” is not a valid repository name"
        }
    }
}

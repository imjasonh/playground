import Foundation

/// A parsed `WWW-Authenticate: Bearer …` challenge from a registry 401.
struct BearerChallenge: Equatable {
    var realm: String
    var service: String?
    var scope: String?

    /// Builds the token URL the registry told us to use.
    func tokenURL(fallbackScope: String?) -> URL? {
        guard var components = URLComponents(string: realm) else { return nil }
        var items: [URLQueryItem] = []
        if let service, !service.isEmpty {
            items.append(URLQueryItem(name: "service", value: service))
        }
        if let scope = scope ?? fallbackScope, !scope.isEmpty {
            items.append(URLQueryItem(name: "scope", value: scope))
        }
        if !items.isEmpty {
            components.queryItems = (components.queryItems ?? []) + items
        }
        return components.url
    }

    /// Parses `Bearer realm="…",service="…",scope="…"`, tolerating unquoted
    /// values and extra whitespace. Returns nil for non-Bearer schemes.
    static func parse(_ header: String) -> BearerChallenge? {
        let trimmed = header.trimmingCharacters(in: .whitespaces)
        guard trimmed.lowercased().hasPrefix("bearer") else { return nil }
        let parameterPart = trimmed.dropFirst("bearer".count).trimmingCharacters(in: .whitespaces)

        var parameters: [String: String] = [:]
        var key = ""
        var value = ""
        var readingKey = true
        var inQuotes = false

        func commit() {
            let trimmedKey = key.trimmingCharacters(in: .whitespaces).lowercased()
            if !trimmedKey.isEmpty {
                parameters[trimmedKey] = value.trimmingCharacters(in: .whitespaces)
            }
            key = ""
            value = ""
            readingKey = true
        }

        for character in parameterPart {
            switch character {
            case "\"":
                inQuotes.toggle()
            case "=" where readingKey && !inQuotes:
                readingKey = false
            case "," where !inQuotes:
                commit()
            default:
                if readingKey {
                    key.append(character)
                } else {
                    value.append(character)
                }
            }
        }
        commit()

        guard let realm = parameters["realm"], !realm.isEmpty else { return nil }
        return BearerChallenge(realm: realm, service: parameters["service"], scope: parameters["scope"])
    }
}

import Foundation

struct CursorAPIResponse {
  let status: Int
  let json: Any
}

final class CursorAPIClient {
  var apiKey: String?
  var mockMode = false
  var apiBase = URL(string: "https://api.cursor.com")!
  var version: String {
    Bundle.main.infoDictionary?["CFBundleShortVersionString"] as? String ?? "0.1.0"
  }

  func request(path: String, method: String, body: Any?) async throws -> CursorAPIResponse {
    let route = path.hasPrefix("/") ? path : "/" + path

    if route == "/health" {
      return CursorAPIResponse(
        status: 200,
        json: [
          "ok": true,
          "mode": mockMode ? "mock" : "live",
          "configured": mockMode || (apiKey?.isEmpty == false),
          "version": version,
          "apiBase": apiBase.absoluteString,
        ]
      )
    }

    if mockMode {
      return try await mockRequest(route: route, method: method, body: body)
    }

    guard let apiKey, !apiKey.isEmpty else {
      return CursorAPIResponse(
        status: 401,
        json: [
          "error": "unconfigured",
          "message": "Set a Cursor API key from the menu (⌘K).",
        ]
      )
    }

    let mapped = try mapRoute(method: method, route: route, body: body)
    var request = URLRequest(url: mapped.url)
    request.httpMethod = mapped.method
    request.setValue("Bearer \(apiKey)", forHTTPHeaderField: "Authorization")
    request.setValue("application/json", forHTTPHeaderField: "Accept")
    if let data = mapped.body {
      request.httpBody = data
      request.setValue("application/json", forHTTPHeaderField: "Content-Type")
    }

    let (data, response) = try await URLSession.shared.data(for: request)
    let status = (response as? HTTPURLResponse)?.statusCode ?? 500
    let json = try JSONSerialization.jsonObject(with: data.isEmpty ? Data("{}".utf8) : data)
    return CursorAPIResponse(status: status, json: json)
  }

  private struct MappedRequest {
    let method: String
    let url: URL
    let body: Data?
  }

  private func mapRoute(method: String, route: String, body: Any?) throws -> MappedRequest {
    let bodyData: Data? = {
      guard let body else { return nil }
      return try? JSONSerialization.data(withJSONObject: body)
    }()

    func url(_ path: String) -> URL {
      apiBase.appendingPathComponent(path.trimmingCharacters(in: CharacterSet(charactersIn: "/")))
    }

    if route == "/me" && method == "GET" {
      return MappedRequest(method: "GET", url: url("/v1/me"), body: nil)
    }
    if route == "/models" && method == "GET" {
      return MappedRequest(method: "GET", url: url("/v1/models"), body: nil)
    }
    if route == "/repositories" && method == "GET" {
      return MappedRequest(method: "GET", url: url("/v1/repositories"), body: nil)
    }
    if route == "/agents" && method == "GET" {
      var components = URLComponents(url: url("/v1/agents"), resolvingAgainstBaseURL: false)!
      components.queryItems = [URLQueryItem(name: "limit", value: "50")]
      return MappedRequest(method: "GET", url: components.url!, body: nil)
    }
    if route == "/agents" && method == "POST" {
      return MappedRequest(method: "POST", url: url("/v1/agents"), body: bodyData)
    }

    let parts = route.split(separator: "/").map(String.init)
    // /agents/:id[/runs|cancel|archive]
    if parts.count >= 2 && parts[0] == "agents" {
      let agentId = parts[1]
      let action = parts.count >= 3 ? parts[2] : nil
      if action == nil && method == "GET" {
        return MappedRequest(method: "GET", url: url("/v1/agents/\(agentId)"), body: nil)
      }
      if action == "runs" && method == "POST" {
        return MappedRequest(method: "POST", url: url("/v1/agents/\(agentId)/runs"), body: bodyData)
      }
      if action == "cancel" && method == "POST" {
        if let dict = body as? [String: Any], let runId = dict["runId"] as? String {
          return MappedRequest(
            method: "POST",
            url: url("/v1/agents/\(agentId)/runs/\(runId)/cancel"),
            body: nil
          )
        }
        return MappedRequest(method: "POST", url: url("/v0/agents/\(agentId)/stop"), body: nil)
      }
      if action == "archive" && method == "POST" {
        return MappedRequest(method: "POST", url: url("/v1/agents/\(agentId)/archive"), body: nil)
      }
      if action == "unarchive" && method == "POST" {
        return MappedRequest(method: "POST", url: url("/v1/agents/\(agentId)/unarchive"), body: nil)
      }
    }

    throw NSError(
      domain: "XeneonCursor",
      code: 404,
      userInfo: [NSLocalizedDescriptionKey: "Unknown route \(route)"]
    )
  }

  private func mockRequest(route: String, method: String, body: Any?) async throws -> CursorAPIResponse {
    // Keep mock behavior in sync with the Node proxy by embedding a small fixture set.
    let fixtures = MockFixtures.shared
    if route == "/me" { return CursorAPIResponse(status: 200, json: fixtures.me) }
    if route == "/models" { return CursorAPIResponse(status: 200, json: fixtures.models) }
    if route == "/repositories" { return CursorAPIResponse(status: 200, json: fixtures.repositories) }
    if route == "/agents" && method == "GET" {
      return CursorAPIResponse(status: 200, json: ["agents": fixtures.agents])
    }
    if route == "/agents" && method == "POST" {
      let created = fixtures.create(body: body)
      return CursorAPIResponse(status: 200, json: created)
    }

    let parts = route.split(separator: "/").map(String.init)
    if parts.count >= 2 && parts[0] == "agents" {
      let agentId = parts[1]
      let action = parts.count >= 3 ? parts[2] : nil
      if action == "runs" && method == "POST" {
        return CursorAPIResponse(status: 200, json: fixtures.followUp(agentId: agentId, body: body))
      }
      if action == "cancel" && method == "POST" {
        return CursorAPIResponse(status: 200, json: fixtures.cancel(agentId: agentId))
      }
      if action == "archive" && method == "POST" {
        return CursorAPIResponse(status: 200, json: fixtures.archive(agentId: agentId))
      }
    }

    return CursorAPIResponse(status: 404, json: ["error": "not_found", "route": route])
  }
}

final class MockFixtures {
  static let shared = MockFixtures()

  var agents: [[String: Any]] = [
    [
      "id": "bc-demo-running-001",
      "name": "Fix flaky auth tests",
      "status": "RUNNING",
      "summary": "Reproducing CI failure and tightening wait helpers…",
      "createdAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-1500)),
      "updatedAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-30)),
      "model": ["id": "composer-2.5"],
      "repos": [["url": "https://github.com/acme/payments", "startingRef": "main"]],
      "url": "https://cursor.com/agents/bc-demo-running-001",
    ],
    [
      "id": "bc-demo-idle-002",
      "name": "Add Xeneon HUD polish",
      "status": "IDLE",
      "summary": "Opened PR with touch-friendly agent cards. Waiting for review.",
      "createdAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-10800)),
      "updatedAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-720)),
      "model": ["id": "claude-4.5-sonnet-thinking"],
      "repos": [["url": "https://github.com/imjasonh/playground", "startingRef": "main"]],
      "url": "https://cursor.com/agents/bc-demo-idle-002",
      "target": [
        "branchName": "cursor/xeneon-cursor-manager",
        "prUrl": "https://github.com/imjasonh/playground/pull/99",
      ],
    ],
    [
      "id": "bc-demo-error-003",
      "name": "Migrate webhook handlers",
      "status": "ERROR",
      "summary": "Setup failed: missing CLOUDFLARE_API_TOKEN in environment.",
      "createdAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-21600)),
      "updatedAt": ISO8601DateFormatter().string(from: Date().addingTimeInterval(-5400)),
      "model": ["id": "gpt-5.5"],
      "repos": [["url": "https://github.com/acme/edge-api", "startingRef": "main"]],
      "url": "https://cursor.com/agents/bc-demo-error-003",
    ],
  ]

  let me: [String: Any] = [
    "apiKeyName": "Xeneon Cursor Manager (mock)",
    "userEmail": "you@example.com",
  ]

  let models: [String: Any] = [
    "models": ["composer-2.5", "claude-4.5-sonnet-thinking", "gpt-5.5"],
  ]

  let repositories: [String: Any] = [
    "repositories": [
      [
        "owner": "imjasonh",
        "name": "playground",
        "repository": "https://github.com/imjasonh/playground",
      ],
    ],
  ]

  func create(body: Any?) -> [String: Any] {
    let prompt = ((body as? [String: Any])?["prompt"] as? [String: Any])?["text"] as? String ?? "New agent"
    let id = "bc-demo-new-\(Int(Date().timeIntervalSince1970))"
    let agent: [String: Any] = [
      "id": id,
      "name": String(prompt.prefix(48)),
      "status": "CREATING",
      "summary": "Provisioning cloud VM…",
      "createdAt": ISO8601DateFormatter().string(from: Date()),
      "updatedAt": ISO8601DateFormatter().string(from: Date()),
      "repos": (body as? [String: Any])?["repos"] ?? [],
      "url": "https://cursor.com/agents/\(id)",
    ]
    agents.insert(agent, at: 0)
    return ["agent": agent, "run": ["id": "run-\(id)", "status": "CREATING"]]
  }

  func followUp(agentId: String, body: Any?) -> [String: Any] {
    if let idx = agents.firstIndex(where: { ($0["id"] as? String) == agentId }) {
      agents[idx]["status"] = "RUNNING"
      let text = ((body as? [String: Any])?["prompt"] as? [String: Any])?["text"] as? String ?? ""
      agents[idx]["summary"] = "Follow-up: \(text.prefix(80))"
      agents[idx]["updatedAt"] = ISO8601DateFormatter().string(from: Date())
    }
    return ["run": ["id": "run-follow-\(agentId)", "status": "RUNNING", "agentId": agentId]]
  }

  func cancel(agentId: String) -> [String: Any] {
    if let idx = agents.firstIndex(where: { ($0["id"] as? String) == agentId }) {
      agents[idx]["status"] = "IDLE"
      agents[idx]["summary"] = "Run cancelled from Xeneon HUD."
    }
    return ["id": agentId, "status": "IDLE"]
  }

  func archive(agentId: String) -> [String: Any] {
    agents.removeAll { ($0["id"] as? String) == agentId }
    return ["id": agentId, "archived": true]
  }
}

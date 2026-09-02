import Foundation

/// Queues prompts from Shortcuts, App Intents, and deep links into Device Agent.
@MainActor
final class AgentInbox: ObservableObject {
    static let shared = AgentInbox()

    @Published private(set) var pendingRun: AgentPendingRun?
    /// When true, the launcher should push Device Agent.
    @Published var shouldOpenExperiment = false

    private let defaultsKey = "deviceAgent.pendingRun"

    private init() {
        if let data = UserDefaults.standard.data(forKey: defaultsKey),
           let run = try? JSONDecoder().decode(AgentPendingRun.self, from: data) {
            pendingRun = run
            if !run.prompt.isEmpty {
                shouldOpenExperiment = true
            }
        }
    }

    func enqueue(
        prompt: String,
        source: AgentRunSource,
        preferVoice: Bool = false,
        url: String? = nil
    ) {
        let trimmedURL = url?.trimmingCharacters(in: .whitespacesAndNewlines)
        let run = AgentPendingRun(
            prompt: prompt.trimmingCharacters(in: .whitespacesAndNewlines),
            source: source,
            preferVoice: preferVoice,
            url: (trimmedURL?.isEmpty == false) ? trimmedURL : nil
        )
        pendingRun = run
        persist(run)
        shouldOpenExperiment = true
    }

    /// Queues a browser drive: open `url` (when http/https), then run `prompt`.
    func enqueueBrowserDrive(
        url: URL,
        prompt: String = "",
        source: AgentRunSource = .shortcut,
        preferVoice: Bool = false
    ) {
        enqueue(
            prompt: prompt,
            source: source,
            preferVoice: preferVoice,
            url: url.absoluteString
        )
    }

    func consumePendingRun() -> AgentPendingRun? {
        let run = pendingRun
        pendingRun = nil
        shouldOpenExperiment = false
        UserDefaults.standard.removeObject(forKey: defaultsKey)
        return run
    }

    func handleOpenURL(_ url: URL) -> Bool {
        guard url.scheme?.lowercased() == "playground" else { return false }
        let host = (url.host ?? "").lowercased()
        guard host == "device-agent" || host == "agent" else { return false }

        let items = URLComponents(url: url, resolvingAgainstBaseURL: false)?.queryItems ?? []
        let prompt = items.first(where: { $0.name == "prompt" })?.value?.removingPercentEncoding ?? ""
        let pageURL = items.first(where: { $0.name == "url" })?.value?.removingPercentEncoding
        let voice = items.first(where: { $0.name == "voice" })?.value == "1"

        enqueue(prompt: prompt, source: .deepLink, preferVoice: voice, url: pageURL)
        return true
    }

    private func persist(_ run: AgentPendingRun) {
        if let data = try? JSONEncoder().encode(run) {
            UserDefaults.standard.set(data, forKey: defaultsKey)
        }
    }
}

import Foundation
import UIKit

/// A long-horizon item Device Agent should re-check on a schedule.
struct AgentWatch: Identifiable, Equatable, Codable {
    var id: UUID
    var title: String
    /// Prompt fed to the agent when this watch is due.
    var prompt: String
    /// Minimum hours between automatic checks.
    var intervalHours: Double
    var lastCheckedAt: Date?
    var createdAt: Date
    var isPaused: Bool

    init(
        id: UUID = UUID(),
        title: String,
        prompt: String,
        intervalHours: Double = 24,
        lastCheckedAt: Date? = nil,
        createdAt: Date = Date(),
        isPaused: Bool = false
    ) {
        self.id = id
        self.title = title
        self.prompt = prompt
        self.intervalHours = max(1, intervalHours)
        self.lastCheckedAt = lastCheckedAt
        self.createdAt = createdAt
        self.isPaused = isPaused
    }

    func isDue(at date: Date = Date()) -> Bool {
        guard !isPaused else { return false }
        guard let lastCheckedAt else { return true }
        return date.timeIntervalSince(lastCheckedAt) >= intervalHours * 3600
    }
}

/// Persisted watches + automation setup heuristics (no API to read Shortcuts Automations).
@MainActor
final class AgentWatchStore: ObservableObject {
    static let shared = AgentWatchStore()

    @Published private(set) var watches: [AgentWatch] = []
    /// Last time Check Device Agent watches ran from Shortcuts / Siri / Automation.
    @Published private(set) var lastAutomaticCheckAt: Date?
    /// User said they created a repeating Automation. Honor system only.
    @Published var userMarkedAutomationConfigured: Bool {
        didSet { persist() }
    }

    private let defaults: UserDefaults
    private let watchesKey = "deviceAgent.watches.v1"
    private let lastCheckKey = "deviceAgent.watches.lastAutomaticCheck"
    private let configuredKey = "deviceAgent.watches.automationConfigured"

    init(userDefaults: UserDefaults = .standard) {
        self.defaults = userDefaults
        if let data = userDefaults.data(forKey: watchesKey),
           let decoded = try? JSONDecoder().decode([AgentWatch].self, from: data)
        {
            watches = decoded
        }
        if let ts = userDefaults.object(forKey: lastCheckKey) as? Date {
            lastAutomaticCheckAt = ts
        }
        userMarkedAutomationConfigured = userDefaults.bool(forKey: configuredKey)
    }

    private var hasActiveWatch: Bool {
        watches.contains { !$0.isPaused }
    }

    /// Suggest creating or recreating the Automation when active watches need wakes.
    var needsAutomationNudge: Bool {
        guard hasActiveWatch else { return false }
        if !userMarkedAutomationConfigured { return true }
        return isAutomaticCheckStale
    }

    /// True when the user claimed setup but no check arrived within the slack window.
    var isAutomaticCheckStale: Bool {
        guard userMarkedAutomationConfigured, hasActiveWatch else { return false }
        guard let lastAutomaticCheckAt else { return true }
        return Date().timeIntervalSince(lastAutomaticCheckAt) > staleSlackSeconds
    }

    /// How long after the tightest watch interval before checks look stale.
    var staleSlackSeconds: TimeInterval {
        let minIntervalHours = watches
            .filter { !$0.isPaused }
            .map(\.intervalHours)
            .min() ?? 24
        // 1.5× interval, at least 18h, so a daily Automation isn’t flagged overnight.
        return max(18 * 3600, minIntervalHours * 3600 * 1.5)
    }

    var lastAutomaticCheckSummary: String {
        guard let lastAutomaticCheckAt else {
            return "No automatic check yet"
        }
        let formatter = RelativeDateTimeFormatter()
        formatter.unitsStyle = .full
        return "Last automatic check \(formatter.localizedString(for: lastAutomaticCheckAt, relativeTo: Date()))"
    }

    func addWatch(title: String, prompt: String, intervalHours: Double) {
        let trimmedTitle = title.trimmingCharacters(in: .whitespacesAndNewlines)
        let trimmedPrompt = prompt.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmedTitle.isEmpty, !trimmedPrompt.isEmpty else { return }
        watches.append(
            AgentWatch(title: trimmedTitle, prompt: trimmedPrompt, intervalHours: intervalHours)
        )
        persist()
    }

    func removeWatch(id: UUID) {
        watches.removeAll { $0.id == id }
        persist()
    }

    func setPaused(id: UUID, paused: Bool) {
        guard let index = watches.firstIndex(where: { $0.id == id }) else { return }
        watches[index].isPaused = paused
        persist()
    }

    func dueWatches(at date: Date = Date()) -> [AgentWatch] {
        watches.filter { $0.isDue(at: date) }
    }

    /// Records a Shortcuts / Siri / Automation wake and marks due watches checked.
    @discardableResult
    func recordAutomaticCheck(at date: Date = Date()) -> [AgentWatch] {
        lastAutomaticCheckAt = date
        let due = dueWatches(at: date)
        for watch in due {
            guard let index = watches.firstIndex(where: { $0.id == watch.id }) else { continue }
            watches[index].lastCheckedAt = date
        }
        persist()
        return due
    }

    func makeCheckPrompt(for due: [AgentWatch]) -> String {
        guard !due.isEmpty else {
            return "No Device Agent watches are due. Reply briefly that everything is quiet."
        }
        let lines = due.enumerated().map { index, watch in
            "\(index + 1). \(watch.title): \(watch.prompt)"
        }
        return """
        Check these Device Agent watches. For each, use tools if needed, then give a short status.
        Prefer Observe-mode tools (no writes unless Act mode is already on).

        \(lines.joined(separator: "\n"))
        """
    }

    func openShortcutsApp() {
        // Undocumented paths first; fall back to Shortcuts root.
        let candidates = [
            URL(string: "shortcuts://create-automation"),
            URL(string: "shortcuts://automations"),
            URL(string: "shortcuts://"),
        ].compactMap { $0 }
        for url in candidates {
            UIApplication.shared.open(url)
            return
        }
    }

    private func persist() {
        if let data = try? JSONEncoder().encode(watches) {
            defaults.set(data, forKey: watchesKey)
        }
        defaults.set(lastAutomaticCheckAt, forKey: lastCheckKey)
        defaults.set(userMarkedAutomationConfigured, forKey: configuredKey)
    }
}

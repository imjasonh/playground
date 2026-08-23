import Foundation
import UniformTypeIdentifiers

/// Stages prompts and files from Shortcuts, deep links, and in-app picks.
/// Host-only for now (no App Group / share appex — that needs signing bootstrap).
@MainActor
final class AgentInbox: ObservableObject {
    static let shared = AgentInbox()

    @Published private(set) var attachments: [AgentAttachment] = []
    @Published private(set) var pendingRun: AgentPendingRun?
    /// When true, the launcher should push Device Agent.
    @Published var shouldOpenExperiment = false

    private let defaultsKey = "deviceAgent.pendingRun"
    private let fileManager = FileManager.default

    var inboxDirectory: URL {
        let base = fileManager.urls(for: .applicationSupportDirectory, in: .userDomainMask).first
            ?? fileManager.temporaryDirectory
        let dir = base.appendingPathComponent("DeviceAgent/Inbox", isDirectory: true)
        if !fileManager.fileExists(atPath: dir.path) {
            try? fileManager.createDirectory(at: dir, withIntermediateDirectories: true)
        }
        return dir
    }

    private init() {
        reloadAttachments()
        if let data = UserDefaults.standard.data(forKey: defaultsKey),
           let run = try? JSONDecoder().decode(AgentPendingRun.self, from: data) {
            pendingRun = run
            if !run.prompt.isEmpty || !run.attachmentIDs.isEmpty {
                shouldOpenExperiment = true
            }
        }
    }

    func reloadAttachments() {
        let dir = inboxDirectory
        let urls = (try? fileManager.contentsOfDirectory(
            at: dir,
            includingPropertiesForKeys: [.fileSizeKey, .contentTypeKey],
            options: [.skipsHiddenFiles]
        )) ?? []
        attachments = urls.compactMap { url in
            let values = try? url.resourceValues(forKeys: [.fileSizeKey, .contentTypeKey])
            let name = url.lastPathComponent
            guard let id = uuidPrefix(from: name) else { return nil }
            let relative = "DeviceAgent/Inbox/\(name)"
            return AgentAttachment(
                id: id,
                filename: stripUUIDPrefix(name),
                relativePath: relative,
                utTypeIdentifier: values?.contentType?.identifier,
                byteCount: values?.fileSize ?? 0
            )
        }
        .sorted { $0.filename.localizedCaseInsensitiveCompare($1.filename) == .orderedAscending }
    }

    @discardableResult
    func importFile(from sourceURL: URL, preferredName: String? = nil, utType: UTType? = nil) throws -> AgentAttachment {
        let id = UUID()
        let name = preferredName ?? sourceURL.lastPathComponent
        let safe = sanitizeFilename(name)
        let stored = "\(id.uuidString)_\(safe)"
        let dest = inboxDirectory.appendingPathComponent(stored)

        let scoped = sourceURL.startAccessingSecurityScopedResource()
        defer {
            if scoped { sourceURL.stopAccessingSecurityScopedResource() }
        }

        if fileManager.fileExists(atPath: dest.path) {
            try fileManager.removeItem(at: dest)
        }
        try fileManager.copyItem(at: sourceURL, to: dest)

        let size = (try? dest.resourceValues(forKeys: [.fileSizeKey]).fileSize) ?? 0
        let attachment = AgentAttachment(
            id: id,
            filename: safe,
            relativePath: "DeviceAgent/Inbox/\(stored)",
            utTypeIdentifier: utType?.identifier ?? UTType(filenameExtension: dest.pathExtension)?.identifier,
            byteCount: size
        )
        reloadAttachments()
        return attachment
    }

    func fileURL(for attachment: AgentAttachment) -> URL? {
        let base = fileManager.urls(for: .applicationSupportDirectory, in: .userDomainMask).first
            ?? fileManager.temporaryDirectory
        let url = base.appendingPathComponent(attachment.relativePath)
        return fileManager.fileExists(atPath: url.path) ? url : nil
    }

    func enqueue(
        prompt: String,
        source: AgentRunSource,
        mode: AgentMode = .act,
        preferVoice: Bool = false,
        attachmentIDs: [UUID] = []
    ) {
        let run = AgentPendingRun(
            prompt: prompt.trimmingCharacters(in: .whitespacesAndNewlines),
            source: source,
            mode: mode,
            preferVoice: preferVoice,
            attachmentIDs: attachmentIDs
        )
        pendingRun = run
        persist(run)
        shouldOpenExperiment = true
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
        let voice = items.first(where: { $0.name == "voice" })?.value == "1"
        let modeRaw = items.first(where: { $0.name == "mode" })?.value ?? AgentMode.act.rawValue
        let mode = AgentMode(rawValue: modeRaw) ?? .act

        enqueue(prompt: prompt, source: .deepLink, mode: mode, preferVoice: voice)
        return true
    }

    private func persist(_ run: AgentPendingRun) {
        if let data = try? JSONEncoder().encode(run) {
            UserDefaults.standard.set(data, forKey: defaultsKey)
        }
    }

    private func sanitizeFilename(_ name: String) -> String {
        let cleaned = name.replacingOccurrences(of: "/", with: "-")
            .replacingOccurrences(of: ":", with: "-")
        return cleaned.isEmpty ? "file" : cleaned
    }

    private func uuidPrefix(from filename: String) -> UUID? {
        let parts = filename.split(separator: "_", maxSplits: 1)
        guard let first = parts.first else { return nil }
        return UUID(uuidString: String(first))
    }

    private func stripUUIDPrefix(_ filename: String) -> String {
        let parts = filename.split(separator: "_", maxSplits: 1)
        if parts.count == 2, UUID(uuidString: String(parts[0])) != nil {
            return String(parts[1])
        }
        return filename
    }
}

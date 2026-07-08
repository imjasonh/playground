import AppKit
import Foundation

final class UpdateChecker {
  static let shared = UpdateChecker()

  private var repo = "imjasonh/playground"
  private var assetName = "XeneonCursor-macos.zip"
  private var checking = false

  func configure(repo: String, assetName: String) {
    self.repo = repo
    self.assetName = assetName
  }

  func checkForUpdates(interactive: Bool) {
    guard !checking else { return }
    checking = true

    Task {
      defer { Task { @MainActor in self.checking = false } }
      do {
        let latest = try await fetchLatestRelease()
        let current = Bundle.main.infoDictionary?["CFBundleShortVersionString"] as? String ?? "0.0.0"
        await MainActor.run {
          if isNewer(latest.tag, than: current) {
            presentUpdate(latest: latest, current: current)
          } else if interactive {
            presentUpToDate(current: current)
          }
        }
      } catch {
        await MainActor.run {
          if interactive {
            let alert = NSAlert()
            alert.messageText = "Update check failed"
            alert.informativeText = error.localizedDescription
            alert.alertStyle = .warning
            alert.addButton(withTitle: "OK")
            alert.runModal()
          }
        }
      }
    }
  }

  private struct ReleaseInfo {
    let tag: String
    let htmlURL: URL
    let assetURL: URL?
  }

  private func fetchLatestRelease() async throws -> ReleaseInfo {
    let url = URL(string: "https://api.github.com/repos/\(repo)/releases?per_page=30")!
    var request = URLRequest(url: url)
    request.setValue("application/vnd.github+json", forHTTPHeaderField: "Accept")
    request.setValue("XeneonCursor", forHTTPHeaderField: "User-Agent")

    let (data, response) = try await URLSession.shared.data(for: request)
    let status = (response as? HTTPURLResponse)?.statusCode ?? 500
    guard status == 200 else {
      throw NSError(
        domain: "XeneonCursor",
        code: status,
        userInfo: [NSLocalizedDescriptionKey: "GitHub returned HTTP \(status)"]
      )
    }

    guard let list = try JSONSerialization.jsonObject(with: data) as? [[String: Any]] else {
      throw NSError(domain: "XeneonCursor", code: 1, userInfo: [NSLocalizedDescriptionKey: "Invalid release JSON"])
    }

    for json in list {
      let rawTag = json["tag_name"] as? String ?? ""
      guard rawTag.hasPrefix("xeneon-cursor-v") else { continue }
      let tag = rawTag.replacingOccurrences(of: "xeneon-cursor-v", with: "")
      let html = URL(string: json["html_url"] as? String ?? "https://github.com/\(repo)/releases")!
      var assetURL: URL?
      if let assets = json["assets"] as? [[String: Any]] {
        if let match = assets.first(where: { ($0["name"] as? String) == assetName }) {
          assetURL = URL(string: match["browser_download_url"] as? String ?? "")
        }
      }
      guard assetURL != nil else { continue }
      return ReleaseInfo(tag: tag, htmlURL: html, assetURL: assetURL)
    }

    throw NSError(
      domain: "XeneonCursor",
      code: 404,
      userInfo: [NSLocalizedDescriptionKey: "No xeneon-cursor release found"]
    )
  }

  private func presentUpdate(latest: ReleaseInfo, current: String) {
    let alert = NSAlert()
    alert.messageText = "Update available"
    alert.informativeText = "Xeneon Cursor \(latest.tag) is available (you have \(current))."
    alert.alertStyle = .informational
    alert.addButton(withTitle: "Download")
    alert.addButton(withTitle: "Later")
    let response = alert.runModal()
    if response == .alertFirstButtonReturn {
      NSWorkspace.shared.open(latest.assetURL ?? latest.htmlURL)
    }
  }

  private func presentUpToDate(current: String) {
    let alert = NSAlert()
    alert.messageText = "You’re up to date"
    alert.informativeText = "Xeneon Cursor \(current) is the latest release."
    alert.alertStyle = .informational
    alert.addButton(withTitle: "OK")
    alert.runModal()
  }

  func isNewer(_ latest: String, than current: String) -> Bool {
    let l = latest.split(separator: ".").compactMap { Int($0) }
    let c = current.split(separator: ".").compactMap { Int($0) }
    let count = max(l.count, c.count)
    for i in 0..<count {
      let lv = i < l.count ? l[i] : 0
      let cv = i < c.count ? c[i] : 0
      if lv != cv { return lv > cv }
    }
    return false
  }
}

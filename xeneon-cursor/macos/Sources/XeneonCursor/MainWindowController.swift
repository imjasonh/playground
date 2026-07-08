import AppKit
import WebKit

final class MainWindowController: NSWindowController, NSWindowDelegate {
  private let hudController = HUDViewController()

  convenience init() {
    let window = NSWindow(
      contentRect: NSRect(x: 0, y: 0, width: 2560, height: 720),
      styleMask: [.titled, .closable, .miniaturizable, .resizable, .fullSizeContentView],
      backing: .buffered,
      defer: false
    )
    window.title = "Xeneon Cursor"
    window.titlebarAppearsTransparent = true
    window.minSize = NSSize(width: 1100, height: 520)
    window.collectionBehavior = [.fullScreenPrimary, .managed]
    window.backgroundColor = NSColor(calibratedRed: 0.04, green: 0.06, blue: 0.08, alpha: 1)
    window.isReleasedWhenClosed = false
    self.init(window: window)
    window.delegate = self
    window.contentViewController = hudController
    window.center()
  }

  func ensureConfigured() {
    if KeychainStore.loadAPIKey() == nil {
      promptForApiKey(allowSkip: true)
    }
  }

  func promptForApiKey(allowSkip: Bool = false) {
    let alert = NSAlert()
    alert.messageText = "Cursor API Key"
    alert.informativeText = """
    Paste a Cloud Agents API key from cursor.com/dashboard/api.
    It is stored in your macOS Keychain and never shipped in the UI bundle.
    Leave blank and choose Mock to explore the HUD offline.
    """
    alert.alertStyle = .informational

    let input = NSSecureTextField(frame: NSRect(x: 0, y: 0, width: 360, height: 24))
    input.stringValue = KeychainStore.loadAPIKey() ?? ""
    alert.accessoryView = input
    alert.addButton(withTitle: "Save")
    if allowSkip {
      alert.addButton(withTitle: "Use Mock Data")
    }
    alert.addButton(withTitle: "Cancel")

    let response = alert.runModal()
    if response == .alertFirstButtonReturn {
      let value = input.stringValue.trimmingCharacters(in: .whitespacesAndNewlines)
      if value.isEmpty {
        KeychainStore.deleteAPIKey()
        hudController.setMockMode(true)
      } else {
        KeychainStore.saveAPIKey(value)
        hudController.setMockMode(false)
        hudController.reload()
      }
    } else if allowSkip && response == .alertSecondButtonReturn {
      KeychainStore.deleteAPIKey()
      hudController.setMockMode(true)
      hudController.reload()
    }
  }
}

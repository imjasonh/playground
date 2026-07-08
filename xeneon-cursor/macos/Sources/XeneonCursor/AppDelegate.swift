import AppKit
import Foundation

final class AppDelegate: NSObject, NSApplicationDelegate {
  private var windowController: MainWindowController?
  private var statusItem: NSStatusItem?

  func applicationDidFinishLaunching(_ notification: Notification) {
    UpdateChecker.shared.configure(
      repo: ProcessInfo.processInfo.environment["XENEON_GITHUB_REPO"] ?? "imjasonh/playground",
      assetName: "XeneonCursor-macos.zip"
    )

    let controller = MainWindowController()
    windowController = controller
    controller.showWindow(nil)
    placeOnPreferredDisplay(controller.window)

    setupMenu()
    setupStatusItem()
    NSApp.activate(ignoringOtherApps: true)

    DispatchQueue.main.asyncAfter(deadline: .now() + 0.4) {
      controller.ensureConfigured()
      UpdateChecker.shared.checkForUpdates(interactive: false)
    }
  }

  func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool {
    true
  }

  private func setupMenu() {
    let mainMenu = NSMenu()

    let appMenuItem = NSMenuItem()
    mainMenu.addItem(appMenuItem)
    let appMenu = NSMenu()
    appMenuItem.submenu = appMenu
    appMenu.addItem(
      withTitle: "About Xeneon Cursor",
      action: #selector(showAbout),
      keyEquivalent: ""
    )
    appMenu.addItem(NSMenuItem.separator())
    appMenu.addItem(
      withTitle: "Set API Key…",
      action: #selector(promptApiKey),
      keyEquivalent: "k"
    )
    appMenu.addItem(
      withTitle: "Check for Updates…",
      action: #selector(checkUpdates),
      keyEquivalent: "u"
    )
    appMenu.addItem(
      withTitle: "Toggle Full Screen",
      action: #selector(toggleFullScreen),
      keyEquivalent: "f"
    )
    appMenu.addItem(NSMenuItem.separator())
    appMenu.addItem(
      withTitle: "Quit Xeneon Cursor",
      action: #selector(NSApplication.terminate(_:)),
      keyEquivalent: "q"
    )

    let editMenuItem = NSMenuItem()
    mainMenu.addItem(editMenuItem)
    let editMenu = NSMenu(title: "Edit")
    editMenuItem.submenu = editMenu
    editMenu.addItem(withTitle: "Cut", action: #selector(NSText.cut(_:)), keyEquivalent: "x")
    editMenu.addItem(withTitle: "Copy", action: #selector(NSText.copy(_:)), keyEquivalent: "c")
    editMenu.addItem(withTitle: "Paste", action: #selector(NSText.paste(_:)), keyEquivalent: "v")
    editMenu.addItem(withTitle: "Select All", action: #selector(NSText.selectAll(_:)), keyEquivalent: "a")

    NSApp.mainMenu = mainMenu
  }

  private func setupStatusItem() {
    statusItem = NSStatusBar.system.statusItem(withLength: NSStatusItem.variableLength)
    if let button = statusItem?.button {
      button.title = "XC"
      button.toolTip = "Xeneon Cursor"
    }
    let menu = NSMenu()
    menu.addItem(withTitle: "Show HUD", action: #selector(showHUD), keyEquivalent: "")
    menu.addItem(withTitle: "Set API Key…", action: #selector(promptApiKey), keyEquivalent: "")
    menu.addItem(withTitle: "Check for Updates…", action: #selector(checkUpdates), keyEquivalent: "")
    menu.addItem(NSMenuItem.separator())
    menu.addItem(withTitle: "Quit", action: #selector(NSApplication.terminate(_:)), keyEquivalent: "q")
    statusItem?.menu = menu
  }

  @objc private func showHUD() {
    windowController?.showWindow(nil)
    NSApp.activate(ignoringOtherApps: true)
  }

  @objc private func promptApiKey() {
    windowController?.promptForApiKey()
  }

  @objc private func checkUpdates() {
    UpdateChecker.shared.checkForUpdates(interactive: true)
  }

  @objc private func toggleFullScreen() {
    windowController?.window?.toggleFullScreen(nil)
  }

  @objc private func showAbout() {
    let version = Bundle.main.infoDictionary?["CFBundleShortVersionString"] as? String ?? "0.1.0"
    let alert = NSAlert()
    alert.messageText = "Xeneon Cursor"
    alert.informativeText = """
    Version \(version)

    Touch-first Cursor cloud agent manager for the Corsair XENEON EDGE.
    Uses the Cloud Agents API and opens agents in the Cursor macOS app via deeplink.
    """
    alert.alertStyle = .informational
    alert.addButton(withTitle: "OK")
    alert.runModal()
  }

  private func placeOnPreferredDisplay(_ window: NSWindow?) {
    guard let window else { return }
    let screens = NSScreen.screens
    let preferred =
      screens.first(where: { screen in
        let name = screen.localizedName.lowercased()
        return name.contains("xeneon") || name.contains("corsair")
      })
      ?? screens.first(where: { screen in
        let frame = screen.frame
        // Prefer ultrawide strip-like displays (~32:9).
        let ratio = frame.width / max(frame.height, 1)
        return ratio > 2.8 && frame.height <= 900
      })
      ?? screens.last

    guard let preferred else { return }
    let visible = preferred.visibleFrame
    let size = NSSize(width: min(2560, visible.width), height: min(720, visible.height))
    let origin = NSPoint(
      x: visible.midX - size.width / 2,
      y: visible.midY - size.height / 2
    )
    window.setFrame(NSRect(origin: origin, size: size), display: true)
    if screens.count > 1 {
      window.toggleFullScreen(nil)
    }
  }
}

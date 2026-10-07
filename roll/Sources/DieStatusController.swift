import AppKit

final class DieStatusController: NSObject {
    private let statusItem: NSStatusItem
    private let checkForUpdates: () -> Void
    private var die = Die()

    init(checkForUpdates: @escaping () -> Void) {
        statusItem = NSStatusBar.system.statusItem(withLength: NSStatusItem.squareLength)
        self.checkForUpdates = checkForUpdates
        super.init()
        configureButton()
        showCurrentFace()
    }

    private func configureButton() {
        guard let button = statusItem.button else {
            return
        }
        button.target = self
        button.action = #selector(handleClick)
        button.sendAction(on: [.leftMouseUp, .rightMouseUp])
        button.imagePosition = .imageOnly
        button.imageScaling = .scaleProportionallyDown
        button.accessibilityIdentifier = "roll-status"
    }

    private func showCurrentFace() {
        guard let button = statusItem.button else {
            return
        }
        let description = "Die, \(die.statusText)"
        button.image = symbolImage(named: die.symbolName, description: description)
        button.toolTip = "\(die.statusText). Right-click or Control-click to quit."
        button.accessibilityLabel = "Roll"
        button.accessibilityValue = die.statusText
        button.accessibilityHelp = "Right-click or Control-click for updates and quit."
    }

    private func symbolImage(named name: String, description: String) -> NSImage {
        let config = NSImage.SymbolConfiguration(pointSize: 15, weight: .regular)
        let base = NSImage(systemSymbolName: name, accessibilityDescription: description)
            ?? NSImage(systemSymbolName: "die.face.1", accessibilityDescription: description)
            ?? NSImage(size: NSSize(width: 18, height: 18))
        let image = base.withSymbolConfiguration(config) ?? base
        image.isTemplate = true
        return image
    }

    @objc private func handleClick() {
        let event = NSApp.currentEvent
        let rightMouse = event?.type == .rightMouseUp
        let control = event?.modifierFlags.contains(.control) ?? false
        switch StatusClick(rightMouse: rightMouse, control: control) {
        case .roll:
            die.roll()
            showCurrentFace()
        case .menu:
            guard let button = statusItem.button, let event else {
                return
            }
            NSMenu.popUpContextMenu(contextMenu(), with: event, for: button)
        }
    }

    private func contextMenu() -> NSMenu {
        let menu = NSMenu()
        let showing = NSMenuItem(title: die.statusText, action: nil, keyEquivalent: "")
        showing.isEnabled = false
        menu.addItem(showing)
        menu.addItem(.separator())

        let updates = NSMenuItem(
            title: "Check for Updates…",
            action: #selector(checkForUpdatesClicked),
            keyEquivalent: ""
        )
        updates.target = self
        menu.addItem(updates)

        let quit = NSMenuItem(
            title: "Quit Roll",
            action: #selector(quit),
            keyEquivalent: "q"
        )
        quit.target = self
        menu.addItem(quit)
        return menu
    }

    @objc private func checkForUpdatesClicked() {
        NSApp.activate()
        checkForUpdates()
    }

    @objc private func quit() {
        NSApp.terminate(nil)
    }
}

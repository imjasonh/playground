import AppKit

final class CountdownStatusController: NSObject {
    private let statusItem: NSStatusItem
    private let store: CountdownStore
    private let checkForUpdates: () -> Void
    private var board: CountdownBoard
    private var midnightTimer: Timer?

    init(store: CountdownStore = CountdownStore(defaults: .standard), checkForUpdates: @escaping () -> Void) {
        statusItem = NSStatusBar.system.statusItem(withLength: NSStatusItem.variableLength)
        self.store = store
        self.checkForUpdates = checkForUpdates
        board = CountdownBoard(countdowns: store.load())
        super.init()
        configureButton()
        reload()
        scheduleMidnightRefresh()
        let center = NotificationCenter.default
        center.addObserver(
            self,
            selector: #selector(calendarChanged),
            name: .NSCalendarDayChanged,
            object: nil
        )
        center.addObserver(
            self,
            selector: #selector(calendarChanged),
            name: .NSSystemTimeZoneDidChange,
            object: nil
        )
    }

    @objc private func calendarChanged() {
        reload()
        scheduleMidnightRefresh()
    }

    private func configureButton() {
        guard let button = statusItem.button else {
            return
        }
        button.target = self
        button.action = #selector(handleClick)
        button.sendAction(on: [.leftMouseUp, .rightMouseUp])
        button.imagePosition = .imageLeading
        button.imageScaling = .scaleProportionallyDown
        button.imageHugsTitle = true
        button.font = NSFont.menuBarFont(ofSize: 0)
        button.setAccessibilityIdentifier("countdown-status")
    }

    private func reload() {
        let status = board.status(now: Date(), calendar: .current)
        guard let button = statusItem.button else {
            return
        }
        button.image = symbolImage(named: "calendar", description: status.accessibilityValue)
        button.title = status.title
        button.imagePosition = status.title.isEmpty ? .imageOnly : .imageLeading
        button.toolTip = status.toolTip
        button.setAccessibilityLabel("Countdown")
        button.setAccessibilityValue(status.accessibilityValue)
        button.setAccessibilityHelp(status.toolTip)
    }

    private func symbolImage(named name: String, description: String) -> NSImage {
        let config = NSImage.SymbolConfiguration(pointSize: 15, weight: .regular)
        let base = NSImage(systemSymbolName: name, accessibilityDescription: description)
            ?? NSImage(size: NSSize(width: 18, height: 18))
        let image = base.withSymbolConfiguration(config) ?? base
        image.isTemplate = true
        return image
    }

    private func scheduleMidnightRefresh() {
        midnightTimer?.invalidate()
        let calendar = Calendar.current
        guard let next = calendar.nextDate(
            after: Date(),
            matching: DateComponents(hour: 0, minute: 0, second: 1),
            matchingPolicy: .nextTime
        ) else {
            return
        }
        let timer = Timer(fire: next, interval: 0, repeats: false) { [weak self] _ in
            self?.reload()
            self?.scheduleMidnightRefresh()
        }
        RunLoop.main.add(timer, forMode: .common)
        midnightTimer = timer
    }

    @objc private func handleClick() {
        reload()
        guard let button = statusItem.button, let event = NSApp.currentEvent else {
            return
        }
        NSMenu.popUpContextMenu(contextMenu(), with: event, for: button)
    }

    private func contextMenu() -> NSMenu {
        let menu = NSMenu()
        let entries = board.menuEntries(now: Date(), calendar: .current)
        for entry in entries {
            switch entry {
            case .separator:
                menu.addItem(.separator())
            case .countdown(let id, let name, let title):
                let item = NSMenuItem(
                    title: title,
                    action: #selector(deleteClicked(_:)),
                    keyEquivalent: ""
                )
                item.target = self
                item.representedObject = id.uuidString
                item.setAccessibilityIdentifier("countdown-\(id.uuidString)")
                item.setAccessibilityHelp("Delete \(name)")
                menu.addItem(item)
            case .command(let action):
                let item = NSMenuItem(
                    title: action.title,
                    action: selector(for: action),
                    keyEquivalent: action == .quit ? "q" : ""
                )
                item.target = self
                item.setAccessibilityIdentifier(action.accessibilityIdentifier)
                menu.addItem(item)
            }
        }
        return menu
    }

    private func selector(for action: CountdownMenuAction) -> Selector {
        switch action {
        case .newCountdown:
            return #selector(newClicked)
        case .checkForUpdates:
            return #selector(checkForUpdatesClicked)
        case .quit:
            return #selector(quit)
        }
    }

    @objc private func deleteClicked(_ sender: NSMenuItem) {
        guard let raw = sender.representedObject as? String, let id = UUID(uuidString: raw) else {
            return
        }
        confirmDelete(id: id)
    }

    private func confirmDelete(id: UUID) {
        guard let countdown = board.countdowns.first(where: { $0.id == id }) else {
            return
        }
        let alert = NSAlert()
        alert.alertStyle = .warning
        alert.messageText = "Delete \(countdown.title)?"
        alert.addButton(withTitle: "Cancel")
        alert.addButton(withTitle: "Delete")
        if let deleteButton = alert.buttons.last {
            deleteButton.hasDestructiveAction = true
        }
        NSApp.activate()
        guard alert.runModal() == .alertSecondButtonReturn else {
            return
        }
        board = board.removing(id)
        store.save(board.countdowns)
        reload()
    }

    @objc private func newClicked() {
        guard let countdown = promptForCountdown() else {
            return
        }
        board = board.adding(countdown)
        store.save(board.countdowns)
        reload()
    }

    private func promptForCountdown() -> Countdown? {
        var draftTitle = ""
        var draftDate = Date()
        var showMissingDescription = false
        let calendar = Calendar.current

        while true {
            let form = countdownForm(
                title: draftTitle,
                date: draftDate,
                calendar: calendar
            )
            let alert = NSAlert()
            alert.messageText = "New countdown"
            if showMissingDescription {
                alert.informativeText = "Enter a description."
            }
            alert.addButton(withTitle: "Add")
            alert.addButton(withTitle: "Cancel")
            if let cancel = alert.buttons.last {
                cancel.keyEquivalent = "\u{1b}"
            }
            alert.accessoryView = form.container
            alert.window.initialFirstResponder = form.descriptionField

            NSApp.activate()
            let response = alert.runModal()
            guard response == .alertFirstButtonReturn else {
                return nil
            }

            draftTitle = form.descriptionField.stringValue
            draftDate = form.picker.dateValue
            let parts = calendar.dateComponents([.year, .month, .day], from: draftDate)
            guard
                let year = parts.year,
                let month = parts.month,
                let day = parts.day,
                let countdown = Countdown.make(
                    title: draftTitle,
                    year: year,
                    month: month,
                    day: day,
                    id: UUID(),
                    calendar: calendar
                )
            else {
                showMissingDescription = true
                continue
            }
            return countdown
        }
    }

    private func countdownForm(
        title: String,
        date: Date,
        calendar: Calendar
    ) -> (container: NSView, descriptionField: NSTextField, picker: NSDatePicker) {
        let width: CGFloat = 260
        let descriptionLabel = NSTextField(labelWithString: "Description")
        descriptionLabel.setAccessibilityElement(false)
        descriptionLabel.frame = NSRect(x: 0, y: 100, width: width, height: 18)
        let descriptionField = NSTextField(string: title)
        descriptionField.frame = NSRect(x: 0, y: 70, width: width, height: 24)
        descriptionField.setAccessibilityLabel("Description")

        let dateLabel = NSTextField(labelWithString: "Date")
        dateLabel.setAccessibilityElement(false)
        dateLabel.frame = NSRect(x: 0, y: 46, width: width, height: 18)
        let picker = NSDatePicker(frame: NSRect(x: 0, y: 8, width: width, height: 28))
        picker.datePickerStyle = .textFieldAndStepper
        picker.datePickerElements = [.yearMonthDay]
        picker.calendar = calendar
        picker.timeZone = calendar.timeZone
        picker.dateValue = date
        picker.setAccessibilityLabel("Date")

        let container = NSView(frame: NSRect(x: 0, y: 0, width: width, height: 120))
        container.addSubview(descriptionLabel)
        container.addSubview(descriptionField)
        container.addSubview(dateLabel)
        container.addSubview(picker)
        return (container, descriptionField, picker)
    }

    @objc private func checkForUpdatesClicked() {
        NSApp.activate()
        checkForUpdates()
    }

    @objc private func quit() {
        NSApp.terminate(nil)
    }
}

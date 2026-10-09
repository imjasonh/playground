import Foundation

struct Countdown: Codable, Equatable, Identifiable, Sendable {
    var id: UUID
    var title: String
    var year: Int
    var month: Int
    var day: Int

    static func make(
        title: String,
        year: Int,
        month: Int,
        day: Int,
        id: UUID,
        calendar: Calendar
    ) -> Countdown? {
        let trimmed = title.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            return nil
        }
        guard isValid(year: year, month: month, day: day, calendar: calendar) else {
            return nil
        }
        return Countdown(id: id, title: trimmed, year: year, month: month, day: day)
    }

    static func isValid(year: Int, month: Int, day: Int, calendar: Calendar) -> Bool {
        DateComponents(year: year, month: month, day: day).isValidDate(in: calendar)
    }

    /// Whole calendar days from `now` to this date in `calendar`.
    ///
    /// `Calendar` is lenient by default, so an invalid day can roll into the
    /// next month. Reject those before asking for a `Date`.
    func days(from now: Date, calendar: Calendar) -> Int? {
        guard Self.isValid(year: year, month: month, day: day, calendar: calendar) else {
            return nil
        }
        var parts = DateComponents()
        parts.year = year
        parts.month = month
        parts.day = day
        guard let target = calendar.date(from: parts) else {
            return nil
        }
        let start = calendar.startOfDay(for: now)
        let end = calendar.startOfDay(for: target)
        return calendar.dateComponents([.day], from: start, to: end).day
    }
}

enum CountdownFormatting {
    static func menuTitle(name: String, days: Int) -> String {
        "\(name) (\(phrase(days: days)))"
    }

    static func phrase(days: Int) -> String {
        switch days {
        case 0:
            return "today"
        case 1:
            return "1 day"
        case -1:
            return "1 day ago"
        case let count where count > 1:
            return "\(count) days"
        default:
            return "\(-days) days ago"
        }
    }

    static func statusTitle(days: Int) -> String {
        if days == 0 {
            return "Today"
        }
        return "\(days)d"
    }

    static func toolTip(name: String, days: Int) -> String {
        switch days {
        case 0:
            return "\(name) is today"
        case 1:
            return "\(name) in 1 day"
        default:
            return "\(name) in \(days) days"
        }
    }
}

enum CountdownMenuAction: Equatable, Sendable {
    case newCountdown
    case checkForUpdates
    case quit

    var title: String {
        switch self {
        case .newCountdown:
            return "New Countdown…"
        case .checkForUpdates:
            return "Check for Updates…"
        case .quit:
            return "Quit Countdown"
        }
    }

    var accessibilityIdentifier: String {
        switch self {
        case .newCountdown:
            return "countdown-new"
        case .checkForUpdates:
            return "countdown-updates"
        case .quit:
            return "countdown-quit"
        }
    }
}

enum CountdownMenuEntry: Equatable, Sendable {
    case countdown(id: UUID, name: String, title: String)
    case command(CountdownMenuAction)
    case separator
}

struct CountdownStatus: Equatable, Sendable {
    var title: String
    var toolTip: String
    var accessibilityValue: String
}

struct CountdownBoard: Equatable, Sendable {
    var countdowns: [Countdown]

    func adding(_ countdown: Countdown) -> CountdownBoard {
        var copy = self
        copy.countdowns.append(countdown)
        return copy
    }

    func removing(_ id: UUID) -> CountdownBoard {
        var copy = self
        copy.countdowns.removeAll { $0.id == id }
        return copy
    }

    func menuEntries(now: Date, calendar: Calendar) -> [CountdownMenuEntry] {
        var entries: [CountdownMenuEntry] = dated(now: now, calendar: calendar).map { row in
            let title: String
            if let days = row.days {
                title = CountdownFormatting.menuTitle(name: row.countdown.title, days: days)
            } else {
                title = "\(row.countdown.title) (invalid date)"
            }
            return .countdown(id: row.countdown.id, name: row.countdown.title, title: title)
        }
        if !entries.isEmpty {
            entries.append(.separator)
        }
        entries.append(.command(.newCountdown))
        entries.append(.separator)
        entries.append(.command(.checkForUpdates))
        entries.append(.command(.quit))
        return entries
    }

    func status(now: Date, calendar: Calendar) -> CountdownStatus {
        let upcoming = dated(now: now, calendar: calendar).first { row in
            guard let days = row.days else {
                return false
            }
            return days >= 0
        }
        if let upcoming, let days = upcoming.days {
            let tip = CountdownFormatting.toolTip(name: upcoming.countdown.title, days: days)
            return CountdownStatus(
                title: CountdownFormatting.statusTitle(days: days),
                toolTip: tip,
                accessibilityValue: tip
            )
        }
        let tip = countdowns.isEmpty ? "No countdowns" : "No upcoming countdowns"
        return CountdownStatus(title: "", toolTip: tip, accessibilityValue: tip)
    }

    private func dated(now: Date, calendar: Calendar) -> [(countdown: Countdown, days: Int?)] {
        countdowns
            .map { countdown in
                (countdown: countdown, days: countdown.days(from: now, calendar: calendar))
            }
            .sorted(by: Self.menuOrder)
    }

    private static func menuOrder(
        _ lhs: (countdown: Countdown, days: Int?),
        _ rhs: (countdown: Countdown, days: Int?)
    ) -> Bool {
        switch (lhs.days, rhs.days) {
        case let (left?, right?):
            let leftUpcoming = left >= 0
            let rightUpcoming = right >= 0
            if leftUpcoming != rightUpcoming {
                return leftUpcoming
            }
            if left != right {
                return leftUpcoming ? left < right : left > right
            }
        case (.some, .none):
            return true
        case (.none, .some):
            return false
        case (.none, .none):
            break
        }
        if lhs.countdown.title != rhs.countdown.title {
            return lhs.countdown.title < rhs.countdown.title
        }
        return lhs.countdown.id.uuidString < rhs.countdown.id.uuidString
    }
}

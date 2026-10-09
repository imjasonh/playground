import XCTest
@testable import Countdown

final class CountdownTests: XCTestCase {
    func testMenuPhrasesMatchTheRequestedForm() {
        XCTAssertEqual(
            CountdownFormatting.menuTitle(name: "birthday", days: 40),
            "birthday (40 days)"
        )
        XCTAssertEqual(
            CountdownFormatting.menuTitle(name: "anniversary", days: 300),
            "anniversary (300 days)"
        )
        XCTAssertEqual(
            CountdownFormatting.menuTitle(name: "christmas", days: 30),
            "christmas (30 days)"
        )
        XCTAssertEqual(CountdownFormatting.menuTitle(name: "birthday", days: 1), "birthday (1 day)")
        XCTAssertEqual(CountdownFormatting.menuTitle(name: "birthday", days: 0), "birthday (today)")
        XCTAssertEqual(CountdownFormatting.menuTitle(name: "trip", days: -1), "trip (1 day ago)")
        XCTAssertEqual(CountdownFormatting.menuTitle(name: "trip", days: -8), "trip (8 days ago)")
    }

    func testStatusTitleUsesAShortDayCount() {
        XCTAssertEqual(CountdownFormatting.statusTitle(days: 40), "40d")
        XCTAssertEqual(CountdownFormatting.statusTitle(days: 1), "1d")
        XCTAssertEqual(CountdownFormatting.statusTitle(days: 0), "Today")
        XCTAssertEqual(CountdownFormatting.toolTip(name: "christmas", days: 30), "christmas in 30 days")
        XCTAssertEqual(CountdownFormatting.toolTip(name: "birthday", days: 1), "birthday in 1 day")
        XCTAssertEqual(CountdownFormatting.toolTip(name: "birthday", days: 0), "birthday is today")
    }

    func testDaysUntilALaterDate() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 15, calendar: calendar)
        let birthday = try countdown(
            "birthday",
            year: 2026,
            month: 11,
            day: 18,
            id: id("AAAAAAAA-AAAA-AAAA-AAAA-AAAAAAAAAAAA"),
            calendar: calendar
        )
        XCTAssertEqual(birthday.days(from: today, calendar: calendar), 40)
    }

    func testSameDayAndNextDayIgnoreTheClockTime() throws {
        let calendar = utcCalendar()
        let evening = try utcDate(year: 2026, month: 10, day: 9, hour: 23, calendar: calendar)
        let nextMorning = try utcDate(year: 2026, month: 10, day: 10, hour: 0, calendar: calendar)
        let target = try countdown(
            "christmas",
            year: 2026,
            month: 10,
            day: 10,
            id: id("BBBBBBBB-BBBB-BBBB-BBBB-BBBBBBBBBBBB"),
            calendar: calendar
        )
        XCTAssertEqual(target.days(from: evening, calendar: calendar), 1)
        XCTAssertEqual(target.days(from: nextMorning, calendar: calendar), 0)
    }

    func testDaysCrossTheNewYear() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 12, day: 31, hour: 12, calendar: calendar)
        let next = try countdown(
            "new year",
            year: 2027,
            month: 1,
            day: 1,
            id: id("CCCCCCCC-CCCC-CCCC-CCCC-CCCCCCCCCCCC"),
            calendar: calendar
        )
        XCTAssertEqual(next.days(from: today, calendar: calendar), 1)
    }

    func testLeapDayCountsAsACalendarDay() throws {
        let calendar = utcCalendar()
        let leap = try countdown(
            "leap",
            year: 2028,
            month: 3,
            day: 1,
            id: id("DDDDDDDD-DDDD-DDDD-DDDD-DDDDDDDDDDDD"),
            calendar: calendar
        )
        let common = try countdown(
            "common",
            year: 2027,
            month: 3,
            day: 1,
            id: id("EEEEEEEE-EEEE-EEEE-EEEE-EEEEEEEEEEEE"),
            calendar: calendar
        )
        let leapStart = try utcDate(year: 2028, month: 2, day: 28, hour: 12, calendar: calendar)
        let commonStart = try utcDate(year: 2027, month: 2, day: 28, hour: 12, calendar: calendar)
        XCTAssertEqual(leap.days(from: leapStart, calendar: calendar), 2)
        XCTAssertEqual(common.days(from: commonStart, calendar: calendar), 1)
    }

    func testDaylightSavingDoesNotChangeTheDayCount() throws {
        var calendar = Calendar(identifier: .gregorian)
        calendar.timeZone = try XCTUnwrap(TimeZone(identifier: "America/New_York"))
        let today = try XCTUnwrap(
            calendar.date(from: DateComponents(year: 2026, month: 3, day: 8, hour: 12))
        )
        let next = try countdown(
            "spring",
            year: 2026,
            month: 3,
            day: 9,
            id: id("FFFFFFFF-FFFF-FFFF-FFFF-FFFFFFFFFFFF"),
            calendar: calendar
        )
        XCTAssertEqual(next.days(from: today, calendar: calendar), 1)
    }

    func testMenuListsSoonestFirstThenCommands() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        let birthday = try daysFromToday(
            "birthday",
            days: 40,
            uuid: "10000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        let anniversary = try daysFromToday(
            "anniversary",
            days: 300,
            uuid: "10000000-0000-0000-0000-000000000002",
            today: today,
            calendar: calendar
        )
        let christmas = try daysFromToday(
            "christmas",
            days: 30,
            uuid: "10000000-0000-0000-0000-000000000003",
            today: today,
            calendar: calendar
        )
        let board = CountdownBoard(countdowns: [birthday, anniversary, christmas])

        XCTAssertEqual(
            board.menuEntries(now: today, calendar: calendar),
            [
                .countdown(id: christmas.id, name: "christmas", title: "christmas (30 days)"),
                .countdown(id: birthday.id, name: "birthday", title: "birthday (40 days)"),
                .countdown(id: anniversary.id, name: "anniversary", title: "anniversary (300 days)"),
                .separator,
                .command(.newCountdown),
                .separator,
                .command(.checkForUpdates),
                .command(.quit),
            ]
        )
        XCTAssertEqual(CountdownMenuAction.newCountdown.title, "New Countdown…")
        XCTAssertEqual(CountdownMenuAction.checkForUpdates.title, "Check for Updates…")
        XCTAssertEqual(CountdownMenuAction.quit.title, "Quit Countdown")
    }

    func testPastDatesFollowUpcomingOnes() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        let past = try daysFromToday(
            "trip",
            days: -8,
            uuid: "20000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        let soon = try daysFromToday(
            "christmas",
            days: 30,
            uuid: "20000000-0000-0000-0000-000000000002",
            today: today,
            calendar: calendar
        )
        let board = CountdownBoard(countdowns: [past, soon])
        let entries = board.menuEntries(now: today, calendar: calendar)
        XCTAssertEqual(
            Array(entries.prefix(3)),
            [
                .countdown(id: soon.id, name: "christmas", title: "christmas (30 days)"),
                .countdown(id: past.id, name: "trip", title: "trip (8 days ago)"),
                .separator,
            ]
        )
    }

    func testSameDayTiesBreakByTitle() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        let birthday = try daysFromToday(
            "birthday",
            days: 10,
            uuid: "30000000-0000-0000-0000-000000000002",
            today: today,
            calendar: calendar
        )
        let anniversary = try daysFromToday(
            "anniversary",
            days: 10,
            uuid: "30000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        let board = CountdownBoard(countdowns: [birthday, anniversary])
        let names = board.menuEntries(now: today, calendar: calendar).compactMap { entry -> String? in
            if case .countdown(_, let name, _) = entry {
                return name
            }
            return nil
        }
        XCTAssertEqual(names, ["anniversary", "birthday"])
    }

    func testStatusShowsTheSoonestUpcomingDate() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        let birthday = try daysFromToday(
            "birthday",
            days: 40,
            uuid: "40000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        let christmas = try daysFromToday(
            "christmas",
            days: 30,
            uuid: "40000000-0000-0000-0000-000000000002",
            today: today,
            calendar: calendar
        )
        let board = CountdownBoard(countdowns: [birthday, christmas])
        XCTAssertEqual(
            board.status(now: today, calendar: calendar),
            CountdownStatus(
                title: "30d",
                toolTip: "christmas in 30 days",
                accessibilityValue: "christmas in 30 days"
            )
        )
    }

    func testStatusForTodayAndOneDay() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 18, calendar: calendar)
        let due = try daysFromToday(
            "birthday",
            days: 0,
            uuid: "50000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        let tomorrow = try daysFromToday(
            "anniversary",
            days: 1,
            uuid: "50000000-0000-0000-0000-000000000002",
            today: today,
            calendar: calendar
        )
        XCTAssertEqual(
            CountdownBoard(countdowns: [due]).status(now: today, calendar: calendar).title,
            "Today"
        )
        XCTAssertEqual(
            CountdownBoard(countdowns: [tomorrow]).status(now: today, calendar: calendar),
            CountdownStatus(
                title: "1d",
                toolTip: "anniversary in 1 day",
                accessibilityValue: "anniversary in 1 day"
            )
        )
    }

    func testEmptyAndPastBoardsLeaveTheStatusBlank() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        XCTAssertEqual(
            CountdownBoard(countdowns: []).status(now: today, calendar: calendar),
            CountdownStatus(title: "", toolTip: "No countdowns", accessibilityValue: "No countdowns")
        )
        let past = try daysFromToday(
            "trip",
            days: -2,
            uuid: "60000000-0000-0000-0000-000000000001",
            today: today,
            calendar: calendar
        )
        XCTAssertEqual(
            CountdownBoard(countdowns: [past]).status(now: today, calendar: calendar).title,
            ""
        )
        XCTAssertEqual(
            CountdownBoard(countdowns: [past]).status(now: today, calendar: calendar).toolTip,
            "No upcoming countdowns"
        )
        XCTAssertEqual(
            CountdownBoard(countdowns: []).menuEntries(now: today, calendar: calendar),
            [
                .command(.newCountdown),
                .separator,
                .command(.checkForUpdates),
                .command(.quit),
            ]
        )
    }

    func testMakeTrimsTheDescriptionAndRejectsBlankOrInvalidDates() throws {
        let calendar = utcCalendar()
        let kept = try XCTUnwrap(
            Countdown.make(
                title: "  birthday  ",
                year: 2026,
                month: 11,
                day: 18,
                id: id("70000000-0000-0000-0000-000000000001"),
                calendar: calendar
            )
        )
        XCTAssertEqual(kept.title, "birthday")
        XCTAssertNil(
            Countdown.make(
                title: "   ",
                year: 2026,
                month: 11,
                day: 18,
                id: kept.id,
                calendar: calendar
            )
        )
        XCTAssertNil(
            Countdown.make(
                title: "leap",
                year: 2027,
                month: 2,
                day: 29,
                id: kept.id,
                calendar: calendar
            )
        )
        XCTAssertNotNil(
            Countdown.make(
                title: "leap",
                year: 2028,
                month: 2,
                day: 29,
                id: kept.id,
                calendar: calendar
            )
        )
    }

    func testInvalidStoredDateStaysDeletable() throws {
        let calendar = utcCalendar()
        let today = try utcDate(year: 2026, month: 10, day: 9, hour: 12, calendar: calendar)
        let broken = Countdown(
            id: id("80000000-0000-0000-0000-000000000001"),
            title: "leap",
            year: 2027,
            month: 2,
            day: 29
        )
        let board = CountdownBoard(countdowns: [broken])
        XCTAssertEqual(
            board.menuEntries(now: today, calendar: calendar).first,
            .countdown(id: broken.id, name: "leap", title: "leap (invalid date)")
        )
    }

    func testAddingAppendsAndRemovingDropsOnlyThatId() throws {
        let calendar = utcCalendar()
        let first = try countdown(
            "birthday",
            year: 2026,
            month: 11,
            day: 18,
            id: id("90000000-0000-0000-0000-000000000001"),
            calendar: calendar
        )
        let second = try countdown(
            "christmas",
            year: 2026,
            month: 12,
            day: 25,
            id: id("90000000-0000-0000-0000-000000000002"),
            calendar: calendar
        )
        let added = CountdownBoard(countdowns: [second]).adding(first)
        XCTAssertEqual(added.countdowns, [second, first])
        XCTAssertEqual(added.removing(second.id).countdowns, [first])
        XCTAssertEqual(added.removing(UUID()).countdowns, [second, first])
    }
}

final class CountdownStoreTests: XCTestCase {
    private var suite = ""
    private var defaults = UserDefaults()

    override func setUpWithError() throws {
        try super.setUpWithError()
        suite = "countdown.tests.\(UUID().uuidString)"
        defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
    }

    override func tearDownWithError() throws {
        defaults.removePersistentDomain(forName: suite)
        try super.tearDownWithError()
    }

    func testRoundTripPreservesOrder() throws {
        let calendar = utcCalendar()
        let first = try countdown(
            "birthday",
            year: 2026,
            month: 11,
            day: 18,
            id: id("A1000000-0000-0000-0000-000000000001"),
            calendar: calendar
        )
        let second = try countdown(
            "christmas",
            year: 2026,
            month: 12,
            day: 25,
            id: id("A1000000-0000-0000-0000-000000000002"),
            calendar: calendar
        )
        let store = CountdownStore(defaults: defaults)
        XCTAssertEqual(store.load(), [])
        store.save([first, second])
        XCTAssertEqual(store.load(), [first, second])
    }

    func testCorruptDataLoadsAsEmpty() {
        defaults.set(Data("nope".utf8), forKey: CountdownStore.defaultsKey)
        XCTAssertEqual(CountdownStore(defaults: defaults).load(), [])
    }
}

private func utcCalendar() -> Calendar {
    var calendar = Calendar(identifier: .gregorian)
    if let timeZone = TimeZone(secondsFromGMT: 0) {
        calendar.timeZone = timeZone
    }
    calendar.locale = Locale(identifier: "en_US_POSIX")
    return calendar
}

private func utcDate(year: Int, month: Int, day: Int, hour: Int, calendar: Calendar) throws -> Date {
    try XCTUnwrap(calendar.date(from: DateComponents(year: year, month: month, day: day, hour: hour)))
}

private func id(_ uuid: String) -> UUID {
    guard let parsed = UUID(uuidString: uuid) else {
        preconditionFailure("invalid UUID \(uuid)")
    }
    return parsed
}

private func countdown(
    _ title: String,
    year: Int,
    month: Int,
    day: Int,
    id: UUID,
    calendar: Calendar
) throws -> Countdown {
    try XCTUnwrap(
        Countdown.make(title: title, year: year, month: month, day: day, id: id, calendar: calendar)
    )
}

private func daysFromToday(
    _ title: String,
    days: Int,
    uuid: String,
    today: Date,
    calendar: Calendar
) throws -> Countdown {
    let start = calendar.startOfDay(for: today)
    let target = try XCTUnwrap(calendar.date(byAdding: .day, value: days, to: start))
    let parts = calendar.dateComponents([.year, .month, .day], from: target)
    return try countdown(
        title,
        year: try XCTUnwrap(parts.year),
        month: try XCTUnwrap(parts.month),
        day: try XCTUnwrap(parts.day),
        id: id(uuid),
        calendar: calendar
    )
}

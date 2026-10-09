import Foundation

struct CountdownStore {
    static let defaultsKey = "countdowns"

    var defaults: UserDefaults

    func load() -> [Countdown] {
        guard let data = defaults.data(forKey: Self.defaultsKey) else {
            return []
        }
        guard let decoded = try? JSONDecoder().decode([Countdown].self, from: data) else {
            return []
        }
        return decoded
    }

    func save(_ countdowns: [Countdown]) {
        guard let data = try? JSONEncoder().encode(countdowns) else {
            return
        }
        defaults.set(data, forKey: Self.defaultsKey)
    }
}

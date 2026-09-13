import Foundation

/// The last PlaygroundBLE peripheral this iPhone connected to.
struct ESP32BLEPreferredDevice: Equatable {
    static let idKey = "esp32-ble.preferred-peripheral-id"
    static let nameKey = "esp32-ble.preferred-peripheral-name"

    var id: UUID
    var name: String

    static func load(from defaults: UserDefaults) -> ESP32BLEPreferredDevice? {
        guard let raw = defaults.string(forKey: idKey), let id = UUID(uuidString: raw) else {
            return nil
        }
        let stored = defaults.string(forKey: nameKey)?
            .trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        return ESP32BLEPreferredDevice(
            id: id,
            name: stored.isEmpty ? ESP32BLEProtocol.deviceName : stored
        )
    }

    func save(to defaults: UserDefaults) {
        defaults.set(id.uuidString, forKey: Self.idKey)
        defaults.set(name, forKey: Self.nameKey)
    }

    /// True when a just-discovered advertisement is the preferred board and
    /// nothing is already connecting or connected.
    static func shouldReconnect(
        discovered: UUID,
        preferred: UUID?,
        wantsReconnect: Bool,
        isBusy: Bool
    ) -> Bool {
        wantsReconnect && !isBusy && discovered == preferred
    }
}

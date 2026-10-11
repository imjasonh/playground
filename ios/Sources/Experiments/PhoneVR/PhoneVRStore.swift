import Combine
import Foundation

/// Persists Phone VR settings and the last session's measurements.
@MainActor
final class PhoneVRStore: ObservableObject {
    @Published var settings: PhoneVRSettings {
        didSet {
            guard settings != oldValue else { return }
            save(settings, forKey: Self.settingsKey)
        }
    }

    @Published private(set) var lastSummary: VRSessionSummary?

    private let defaults: UserDefaults
    private static let settingsKey = "phoneVR.settings.v1"
    private static let summaryKey = "phoneVR.lastSession.v1"

    init(defaults: UserDefaults = .standard) {
        self.defaults = defaults
        settings = Self.load(PhoneVRSettings.self, forKey: Self.settingsKey, from: defaults) ?? PhoneVRSettings()
        lastSummary = Self.load(VRSessionSummary.self, forKey: Self.summaryKey, from: defaults)
    }

    /// Keeps in-headset calibration and stores the session's measurements.
    func record(_ result: VRSessionResult) {
        settings.profile = result.profile
        lastSummary = result.summary
        save(result.summary, forKey: Self.summaryKey)
    }

    func resetViewer() {
        settings.profile = .standard
    }

    private func save<Value: Encodable>(_ value: Value, forKey key: String) {
        guard let data = try? JSONEncoder().encode(value) else { return }
        defaults.set(data, forKey: key)
    }

    private static func load<Value: Decodable>(_ type: Value.Type, forKey key: String, from defaults: UserDefaults) -> Value? {
        guard let data = defaults.data(forKey: key) else { return nil }
        return try? JSONDecoder().decode(type, from: data)
    }
}

import Foundation
import Security

/// Persisted handshake state. Tests substitute an in-memory store.
@MainActor
protocol AppAttestStoring: AnyObject {
    var keyId: String? { get set }
    var deviceId: String { get }
    var userId: String { get set }
    var token: String? { get set }
    func clearSession()
}

/// UserDefaults for ids/token, Keychain for the App Attest `keyId`.
@MainActor
final class AppAttestUserDefaultsStore: AppAttestStoring {
    static let suiteName = "io.github.imjasonh.playground.app-attest"
    private static let deviceIdKey = "deviceId"
    private static let userIdKey = "userId"
    private static let tokenKey = "token"
    private static let keychainAccount = "keyId"

    private let defaults: UserDefaults

    init(defaults: UserDefaults = UserDefaults(suiteName: AppAttestUserDefaultsStore.suiteName) ?? .standard) {
        self.defaults = defaults
        if defaults.string(forKey: Self.deviceIdKey) == nil {
            defaults.set(UUID().uuidString, forKey: Self.deviceIdKey)
        }
    }

    var keyId: String? {
        get { AppAttestKeychain.read(account: Self.keychainAccount) }
        set {
            if let newValue {
                AppAttestKeychain.write(account: Self.keychainAccount, value: newValue)
            } else {
                AppAttestKeychain.delete(account: Self.keychainAccount)
            }
        }
    }

    var deviceId: String {
        if let existing = defaults.string(forKey: Self.deviceIdKey), !existing.isEmpty {
            return existing
        }
        let created = UUID().uuidString
        defaults.set(created, forKey: Self.deviceIdKey)
        return created
    }

    var userId: String {
        get { defaults.string(forKey: Self.userIdKey) ?? "" }
        set { defaults.set(newValue, forKey: Self.userIdKey) }
    }

    var token: String? {
        get { defaults.string(forKey: Self.tokenKey) }
        set { defaults.set(newValue, forKey: Self.tokenKey) }
    }

    func clearSession() {
        defaults.removeObject(forKey: Self.tokenKey)
        keyId = nil
    }
}

/// In-memory store for unit tests.
@MainActor
final class AppAttestMemoryStore: AppAttestStoring {
    var keyId: String?
    let deviceId: String
    var userId: String
    var token: String?

    init(deviceId: String = "device-test", userId: String = "user-test") {
        self.deviceId = deviceId
        self.userId = userId
    }

    func clearSession() {
        token = nil
        keyId = nil
    }
}

enum AppAttestKeychain {
    static let service = "io.github.imjasonh.playground.app-attest"

    static func read(account: String) -> String? {
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
            kSecReturnData as String: true,
            kSecMatchLimit as String: kSecMatchLimitOne,
        ]
        var item: CFTypeRef?
        let status = SecItemCopyMatching(query as CFDictionary, &item)
        guard status == errSecSuccess, let data = item as? Data else {
            return nil
        }
        return String(data: data, encoding: .utf8)
    }

    static func write(account: String, value: String) {
        delete(account: account)
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
            kSecValueData as String: Data(value.utf8),
            kSecAttrAccessible as String: kSecAttrAccessibleAfterFirstUnlockThisDeviceOnly,
        ]
        _ = SecItemAdd(query as CFDictionary, nil)
    }

    static func delete(account: String) {
        let query: [String: Any] = [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account,
        ]
        _ = SecItemDelete(query as CFDictionary)
    }
}

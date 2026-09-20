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

enum AppAttestStorageKeys {
    static let suiteName = "io.github.imjasonh.playground.app-attest"
    static let deviceId = "deviceId"
    static let userId = "userId"
    static let token = "token"
    static let keychainAccount = "keyId"
}

/// UserDefaults for ids/token, Keychain for the App Attest `keyId`.
@MainActor
final class AppAttestUserDefaultsStore: AppAttestStoring {
    private let defaults: UserDefaults

    init(defaults: UserDefaults? = nil) {
        self.defaults = defaults
            ?? UserDefaults(suiteName: AppAttestStorageKeys.suiteName)
            ?? .standard
        if self.defaults.string(forKey: AppAttestStorageKeys.deviceId) == nil {
            self.defaults.set(UUID().uuidString, forKey: AppAttestStorageKeys.deviceId)
        }
    }

    var keyId: String? {
        get { AppAttestKeychain.read(account: AppAttestStorageKeys.keychainAccount) }
        set {
            if let newValue {
                AppAttestKeychain.write(account: AppAttestStorageKeys.keychainAccount, value: newValue)
            } else {
                AppAttestKeychain.delete(account: AppAttestStorageKeys.keychainAccount)
            }
        }
    }

    var deviceId: String {
        if let existing = defaults.string(forKey: AppAttestStorageKeys.deviceId), !existing.isEmpty {
            return existing
        }
        let created = UUID().uuidString
        defaults.set(created, forKey: AppAttestStorageKeys.deviceId)
        return created
    }

    var userId: String {
        get { defaults.string(forKey: AppAttestStorageKeys.userId) ?? "" }
        set { defaults.set(newValue, forKey: AppAttestStorageKeys.userId) }
    }

    var token: String? {
        get { defaults.string(forKey: AppAttestStorageKeys.token) }
        set { defaults.set(newValue, forKey: AppAttestStorageKeys.token) }
    }

    func clearSession() {
        defaults.removeObject(forKey: AppAttestStorageKeys.token)
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

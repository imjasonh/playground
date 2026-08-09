import Foundation
import Security

/// Persistent bits of App Attest state.
///
/// The Secure Enclave holds the private key; all the app ever gets is a `keyId`
/// naming it. Losing that id doesn't leak anything, it just strands the key, so
/// the app has to attest a fresh one. The `artifact` is Firebase's receipt that
/// the key was already attested, and every later assertion is bound to it.
protocol GCPAuthStateStore: AnyObject {
    var appAttestKeyID: String? { get set }
    var appCheckArtifact: Data? { get set }
    func reset()
}

final class GCPAuthInMemoryStore: GCPAuthStateStore {
    var appAttestKeyID: String?
    var appCheckArtifact: Data?

    init(appAttestKeyID: String? = nil, appCheckArtifact: Data? = nil) {
        self.appAttestKeyID = appAttestKeyID
        self.appCheckArtifact = appCheckArtifact
    }

    func reset() {
        appAttestKeyID = nil
        appCheckArtifact = nil
    }
}

/// Keychain-backed store.
///
/// `AfterFirstUnlockThisDeviceOnly` matches what the state is: a pointer to a
/// key that only exists on this device's Secure Enclave, so syncing it to iCloud
/// or restoring it onto different hardware could only ever produce a key id that
/// no longer resolves.
final class GCPAuthKeychainStore: GCPAuthStateStore {
    private let service: String

    init(service: String = "io.github.imjasonh.playground.gcpauth") {
        self.service = service
    }

    var appAttestKeyID: String? {
        get { read(account: Account.keyID).map { String(decoding: $0, as: UTF8.self) } }
        set { write(account: Account.keyID, data: newValue.map { Data($0.utf8) }) }
    }

    var appCheckArtifact: Data? {
        get { read(account: Account.artifact) }
        set { write(account: Account.artifact, data: newValue) }
    }

    func reset() {
        write(account: Account.keyID, data: nil)
        write(account: Account.artifact, data: nil)
    }

    private enum Account {
        static let keyID = "app-attest-key-id"
        static let artifact = "app-check-artifact"
    }

    private func query(account: String) -> [String: Any] {
        [
            kSecClass as String: kSecClassGenericPassword,
            kSecAttrService as String: service,
            kSecAttrAccount as String: account
        ]
    }

    private func read(account: String) -> Data? {
        var lookup = query(account: account)
        lookup[kSecReturnData as String] = true
        lookup[kSecMatchLimit as String] = kSecMatchLimitOne

        var item: CFTypeRef?
        guard SecItemCopyMatching(lookup as CFDictionary, &item) == errSecSuccess else {
            return nil
        }
        return item as? Data
    }

    private func write(account: String, data: Data?) {
        let base = query(account: account)
        SecItemDelete(base as CFDictionary)
        guard let data else { return }

        var insert = base
        insert[kSecValueData as String] = data
        insert[kSecAttrAccessible as String] = kSecAttrAccessibleAfterFirstUnlockThisDeviceOnly
        SecItemAdd(insert as CFDictionary, nil)
    }
}

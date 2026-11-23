import Foundation
import UserNotifications

/// Sends native macOS notifications for high-severity findings on trusted networks.
/// Guards against XCTest environments where `UNUserNotificationCenter.current()` has no app bundle.
enum NotificationManager {
    private static var isSupportedRuntime: Bool {
        Bundle.main.bundleIdentifier != nil
            && ProcessInfo.processInfo.environment["XCTestConfigurationFilePath"] == nil
    }

    static func requestPermissionIfNeeded() {
        guard isSupportedRuntime else { return }
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound, .badge]) { _, _ in }
    }

    static func post(finding: Finding) {
        guard isSupportedRuntime else { return }
        let content = UNMutableNotificationContent()
        content.title = "Lantern: \(finding.displayHeadline)"
        content.body = finding.displayBody
        content.sound = finding.severity == .critical ? .defaultCritical : .default

        let request = UNNotificationRequest(
            identifier: "lantern.\(finding.dedupeKey)",
            content: content,
            trigger: nil
        )
        UNUserNotificationCenter.current().add(request)
    }
}

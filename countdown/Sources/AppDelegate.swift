import AppKit

final class AppDelegate: NSObject, NSApplicationDelegate {
    private var status: CountdownStatusController?
    private let updater = SparkleUpdater()

    func applicationWillFinishLaunching(_ notification: Notification) {
        _ = NSApp.setActivationPolicy(.accessory)
    }

    func applicationDidFinishLaunching(_ notification: Notification) {
        status = CountdownStatusController { [updater] in
            updater.checkForUpdates()
        }
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool {
        false
    }
}

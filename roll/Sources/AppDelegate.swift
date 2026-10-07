import AppKit

@main
final class AppDelegate: NSObject, NSApplicationDelegate {
    private var status: DieStatusController?
    private let updater = SparkleUpdater()

    func applicationWillFinishLaunching(_ notification: Notification) {
        _ = NSApp.setActivationPolicy(.accessory)
    }

    func applicationDidFinishLaunching(_ notification: Notification) {
        status = DieStatusController { [updater] in
            updater.checkForUpdates()
        }
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool {
        false
    }
}

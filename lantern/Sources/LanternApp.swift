import AppKit
import SwiftUI

@main
struct LanternApp: App {
    @StateObject private var sentinel = SentinelController()
    @StateObject private var updater = SparkleUpdater()

    var body: some Scene {
        MenuBarExtra {
            MenuBarPopoverView()
                .environmentObject(sentinel)
                .environmentObject(updater)
        } label: {
            Label("Lantern", systemImage: sentinel.safeMenuBarSymbol)
        }
        .menuBarExtraStyle(.window)

        Window("Lantern Inspector", id: "inspector") {
            InspectorWindowView()
                .environmentObject(sentinel)
                .environmentObject(updater)
                .frame(minWidth: 820, minHeight: 540)
        }
        .defaultSize(width: 960, height: 640)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
            }
        }
    }
}

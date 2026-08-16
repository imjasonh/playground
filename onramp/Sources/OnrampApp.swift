import SwiftUI

@main
struct OnrampApp: App {
    @StateObject private var updater = SparkleUpdater()

    var body: some Scene {
        WindowGroup {
            ContentView()
        }
        .defaultSize(width: 880, height: 620)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
            }
        }

        MenuBarExtra("Onramp", systemImage: "stethoscope") {
            MenuBarQuickPanel()
        }
        .menuBarExtraStyle(.window)
    }
}

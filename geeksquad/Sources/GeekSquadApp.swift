import SwiftUI

@main
struct GeekSquadApp: App {
    @StateObject private var updater = SparkleUpdater()

    var body: some Scene {
        WindowGroup {
            ContentView()
        }
        .defaultSize(width: 820, height: 560)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
            }
        }
    }
}

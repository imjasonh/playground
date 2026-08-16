import SwiftUI

@main
struct OnrampApp: App {
    @StateObject private var updater = SparkleUpdater()
    @StateObject private var foundationModelsGate = FoundationModelsGateModel()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environmentObject(foundationModelsGate)
        }
        .defaultSize(width: 880, height: 620)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
                Button("Check Apple Intelligence…") {
                    foundationModelsGate.allowPlaybooksWithoutModel = false
                    foundationModelsGate.refresh()
                }
            }
        }

        MenuBarExtra("Onramp", systemImage: "stethoscope") {
            MenuBarQuickPanel()
                .environmentObject(foundationModelsGate)
        }
        .menuBarExtraStyle(.window)
    }
}
